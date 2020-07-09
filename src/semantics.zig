// semantics.zig:
// Generates IR from ASTs.

const std = @import("std");
const assert = std.debug.assert;

const LinkAllocator = @import("linkalloc.zig").LinkAllocator;
const StringTrie = @import("trie.zig").StringTrie;

const grammar = @import("grammar.zig");
const ir = @import("ir.zig");
const Location = grammar.Location;
const ErrorMessage = grammar.ErrorMessage;
const Identifier = @import("identifiers.zig").Identifier;
const IdentifierPool = @import("identifiers.zig").IdentifierPool;
const IdentifierMap = @import("identifiers.zig").IdentifierMap;
const compile_errors = @import("compile_errors.zig");

const ObjectID = union(enum) {
    ClassID: ClassID,
    UnionID: UnionID,
    InterfaceID: InterfaceID,
};

const ObjectBinding = struct {
    binding_location: Location,
    object_id: ObjectID,
};

const PackageBinding = struct {
    binding_location: Location,
    package_id: PackageID,
};

const WorkingPackage = struct {
    /// The index into the `working_packages` array of `Work`.
    id: usize,
    package_name: Identifier,
    work: *Work,

    objects_by_name: IdentifierMap(ObjectBinding),

    pub fn init(work: *Work, name: Identifier, id: usize) WorkingPackage {
        return WorkingPackage{
            .id = id,
            .package_name = name,
            .work = work,
            .objects_by_name = IdentifierMap(ObjectBinding).init(work.top_allocator, work.pool),
        };
    }

    fn deinit(self: *WorkingPackage) void {
        self.objects_by_name.deinit();
    }

    fn defineObject(self: *WorkingPackage, work: *Work, source_id: SourceID, name: Identifier, binding_location: Location, object: ObjectID, error_message: *ErrorMessage) !void {
        if (self.objects_by_name.get(name)) |existing| {
            return compile_errors.ObjectRedefinedErr.err(error_message, .{
                .package_iden = self.package_name,
                .object_iden = name,
                .first_definition_location = existing.binding_location,
                .second_definition_location = binding_location,
            });
        }
        try self.objects_by_name.put(name, ObjectBinding{
            .binding_location = binding_location,
            .object_id = object,
        });
    }

    fn defineClass(self: *WorkingPackage, work: *Work, source_id: SourceID, class_definition: *const grammar.ClassDefinition, error_message: *ErrorMessage) !void {
        const class_id = ObjectID{
            .ClassID = try work.addClass(PackageID{ .id = self.id }, source_id, class_definition),
        };
        const name_id = class_definition.class_name.value;
        try self.defineObject(work, source_id, name_id, class_definition.class_name.location, class_id, error_message);
    }

    fn defineInterface(self: *WorkingPackage, work: *Work, source_id: SourceID, interface_definition: *const grammar.InterfaceDefinition, error_message: *ErrorMessage) !void {
        const interface_id = ObjectID{
            .InterfaceID = try work.addInterface(PackageID{ .id = self.id }, source_id, interface_definition),
        };
        const name_id = interface_definition.interface_name.value;
        try self.defineObject(work, source_id, name_id, interface_definition.interface_name.location, interface_id, error_message);
    }
};

const ConstraintBinding = struct {
    constraint: Constraint,
    constraining_location: Location,
};

const Constraints = struct {
    on_variable: Identifier,
    constraints: std.ArrayList(ConstraintBinding),

    fn init(allocator: *std.mem.Allocator, parameter: Identifier) Constraints {
        return Constraints{
            .on_variable = parameter,
            .constraints = std.ArrayList(ConstraintBinding).init(allocator),
        };
    }

    fn deinit(self: Constraints) void {
        self.constraints.deinit();
    }
};

const TypeVariableBinding = struct {
    type_variable_id: TypeVariableID,
    binding_location: Location,
};

const TypeParameterScope = struct {
    type_parameters_by_name: IdentifierMap(TypeVariableBinding),
    type_parameter_constraints: std.ArrayList(Constraints),
    allocator: *std.mem.Allocator,

    fn init(allocator: *std.mem.Allocator, identifier_pool: *IdentifierPool) TypeParameterScope {
        return .{
            .allocator = allocator,
            .type_parameters_by_name = IdentifierMap(TypeVariableBinding).init(allocator, identifier_pool),
            .type_parameter_constraints = std.ArrayList(Constraints).init(allocator),
        };
    }

    fn deinit(self: *TypeParameterScope) void {
        self.type_parameters_by_name.deinit();
        for (self.type_parameter_constraints) |c| {
            c.deinit();
        }
        self.type_parameter_constraints.deinit();
    }

    fn defineTypeParameter(self: *TypeParameterScope, parameter: grammar.LeafTypeVar, error_message: *ErrorMessage) !void {
        if (self.type_parameters_by_name.get(parameter.value)) |existing_binding| {
            return compile_errors.TypeParameterRedefinedErr.err(error_message, .{
                .first_binding_location = existing_binding.binding_location,
                .second_binding_location = parameter.location,
                .type_parameter_name = parameter.value,
            });
        }
        try self.type_parameters_by_name.put(parameter.value, TypeVariableBinding{
            .type_variable_id = .{ .id = self.type_parameter_constraints.items.len },
            .binding_location = parameter.location,
        });
        try self.type_parameter_constraints.append(Constraints.init(self.allocator, parameter.value));
    }
};

const WorkingClass = struct {
    /// The index into the `working_classes` array of `Work`.
    id: usize,

    /// The index of the containing package in the `working_packages` array of `Work`.
    package_id: PackageID,

    /// The index of the defining source file.
    source_id: SourceID,

    ast: *const grammar.ClassDefinition,

    type_parameter_scope: TypeParameterScope,

    // The list of constraints that this class implements.
    implements: std.ArrayList(Constraint),

    /// A map of type-parameter identifier to index.
    fn deinit(self: *WorkingClass) void {
        self.type_parameters_by_name.deinit();
        for (self.type_parameter_constraints.items) |*tpc| {
            tpc.deinit();
        }
        self.type_parameter_constraints.deinit();
        self.implements.deinit();
    }

    fn init(allocator: *std.mem.Allocator, pool: *IdentifierPool, id: usize, package_id: PackageID, source_id: SourceID, ast: *const grammar.ClassDefinition) WorkingClass {
        return WorkingClass{
            .id = id,
            .package_id = package_id,
            .source_id = source_id,
            .ast = ast,

            .type_parameter_scope = TypeParameterScope.init(allocator, pool),
            .implements = std.ArrayList(Constraint).init(allocator),
        };
    }
};

const WorkingInterface = struct {
    /// The index into the `working_interfaces` array of `Work`.
    id: usize,

    /// The index of the containing package in the `working_packages` array of `Work`.
    package_id: PackageID,

    /// The index of the defining source file.
    source_id: SourceID,

    ast: *const grammar.InterfaceDefinition,

    type_parameter_scope: TypeParameterScope,

    fn getPackageName(self: *const WorkingInterface, work: *Work) Identifier {
        return work.getPackage(self.package_id).package_name;
    }

    fn getName(self: *const WorkingInterface) Identifier {
        return self.ast.interface_name.value;
    }
};

const WorkingFunction = struct {
    /// The index into the `working_functions` array of `Work`.
    id: usize,

    ast: grammar.FunctionDef,
};

const TypeVariableID = struct {
    id: usize,
};

const Type = union(enum) {
    ClassType: ClassType,
    IntType: void,
    StringType: void,
    /// The index into the type-parameters scope stack.
    GenericType: TypeVariableID,
};

const TypeLike = union(enum) {
    Type: Type,
    Constraint: Constraint,
};

const Constraint = union(enum) {
    InterfaceConstraint: InterfaceConstraint,
};

const InterfaceConstraint = struct {
    interface_id: InterfaceID,
    type_arguments: []TypeLike,
};

const ClassType = struct {
    class_id: ClassID,
    type_arguments: []TypeLike,
};

const SourceID = struct { id: usize };
const ClassID = struct { id: usize };
const UnionID = struct { id: usize };
const InterfaceID = struct { id: usize };
const PackageID = struct { id: usize };

const Work = struct {
    top_allocator: *std.mem.Allocator,
    pool: *IdentifierPool,

    arena: std.heap.ArenaAllocator,

    working_packages: std.ArrayList(WorkingPackage),
    working_classes: std.ArrayList(WorkingClass),
    working_interfaces: std.ArrayList(WorkingInterface),
    working_functions: std.ArrayList(WorkingFunction),

    package_ids_by_name: IdentifierMap(usize),

    fn getPackage(self: *Work, package_id: PackageID) *WorkingPackage {
        return &self.working_packages.items[package_id.id];
    }

    fn getClass(self: *Work, class_id: ClassID) *WorkingClass {
        return &self.working_classes.items[class_id.id];
    }

    fn getInterface(self: *Work, interface_id: InterfaceID) *WorkingInterface {
        return &self.working_interfaces.items[interface_id.id];
    }

    fn findPackageByName(self: *Work, name: Identifier, access_location: Location, error_message: *ErrorMessage) !PackageID {
        if (self.package_ids_by_name.get(name)) |package_id| {
            return PackageID{ .id = package_id.* };
        }
        return compile_errors.UnknownPackageReferencedErr.err(error_message, .{
            .package_iden = name,
            .reference_location = access_location,
        });
    }

    fn addClass(self: *Work, package_id: PackageID, source_id: SourceID, ast: *const grammar.ClassDefinition) !ClassID {
        const id = ClassID{ .id = self.working_classes.items.len };
        try self.working_classes.append(WorkingClass.init(
            self.top_allocator,
            self.pool,
            self.working_classes.items.len,
            package_id,
            source_id,
            ast,
        ));
        return id;
    }
    fn addInterface(self: *Work, package_id: PackageID, source_id: SourceID, ast: *const grammar.InterfaceDefinition) !InterfaceID {
        const id = InterfaceID{ .id = self.working_interfaces.items.len };
        try self.working_interfaces.append(WorkingInterface{
            .id = self.working_interfaces.items.len,
            .package_id = package_id,
            .source_id = source_id,
            .ast = ast,
            .type_parameter_scope = TypeParameterScope.init(self.top_allocator, self.pool),
        });
        return id;
    }

    pub fn getPackageByNameOpt(self: *Work, package_name: Identifier) ?PackageID {
        if (self.package_ids_by_name.get(package_name)) |id| {
            return PackageID{ .id = id.* };
        }
        return null;
    }

    pub fn addPackageByName(self: *Work, package_name: Identifier) !PackageID {
        assert(self.getPackageByNameOpt(package_name) == null);

        const new_id = self.working_packages.items.len;
        const package = WorkingPackage.init(self, package_name, new_id);
        try self.working_packages.append(package);
        try self.package_ids_by_name.put(package_name, new_id);
        return PackageID{ .id = new_id };
    }

    fn deinit(self: *Work) void {
        for (self.working_packages.items) |*wp| {
            wp.deinit();
        }
        self.working_packages.deinit();
        self.working_classes.deinit();
        self.working_functions.deinit();
        self.working_interfaces.deinit();
        self.package_ids_by_name.deinit();
        self.arena.deinit();
    }

    pub fn init(top_allocator: *std.mem.Allocator, identifier_pool: *IdentifierPool) Work {
        return Work{
            .top_allocator = top_allocator,
            .pool = identifier_pool,

            .arena = std.heap.ArenaAllocator.init(top_allocator),

            .working_packages = std.ArrayList(WorkingPackage).init(top_allocator),
            .working_classes = std.ArrayList(WorkingClass).init(top_allocator),
            .working_functions = std.ArrayList(WorkingFunction).init(top_allocator),
            .working_interfaces = std.ArrayList(WorkingInterface).init(top_allocator),

            .package_ids_by_name = IdentifierMap(usize).init(top_allocator, identifier_pool),
        };
    }
};

const SourceContext = struct {
    package_id: PackageID,

    referenceable_packages: IdentifierMap(PackageBinding),

    imported_objects: IdentifierMap(ObjectBinding),

    fn importObject(self: *SourceContext, work: *Work, name: Identifier, object_id: ObjectID, binding_location: Location, error_message: *ErrorMessage) !void {
        const package = work.getPackage(self.package_id);
        if (self.imported_objects.get(name) orelse package.objects_by_name.get(name)) |existing| {
            return compile_errors.ObjectReimportedErr.err(error_message, .{
                .object_iden = name,
                .first_binding_location = existing.binding_location,
                .import_location = binding_location,
            });
        }
        try self.imported_objects.put(name, ObjectBinding{
            .object_id = object_id,
            .binding_location = binding_location,
        });
    }

    fn importPackage(self: *SourceContext, work: *Work, name: Identifier, package_id: PackageID, binding_location: Location, error_message: *ErrorMessage) !void {
        const this_package_name = work.getPackage(self.package_id).package_name;
        if (name.eq(this_package_name)) {
            return compile_errors.PackageImportSelfErr.err(error_message, .{
                .package_name = this_package_name,
                .import_location = binding_location,
            });
        }

        if (self.referenceable_packages.get(name)) |existing| {
            return compile_errors.PackageReimportedErr.err(error_message, .{
                .package_iden = name,
                .first_binding_location = existing.binding_location,
                .import_location = binding_location,
            });
        }

        try self.referenceable_packages.put(name, PackageBinding{
            .package_id = package_id,
            .binding_location = binding_location,
        });
    }

    fn resolveQualifiedObject(self: *const SourceContext, work: *const Work, object_iden: grammar.LeafTypeIden, package_iden: *const grammar.PackageQualifier, error_message: *ErrorMessage) !ObjectID {
        unreachable;
    }

    /// Resolves an object referenced in this package.
    /// Produces a CompileError if such an object doesn't exist.
    fn resolveUnqualifiedObject(self: *const SourceContext, work: *Work, object_iden: grammar.LeafTypeIden, error_message: *ErrorMessage) !ObjectID {
        if (self.imported_objects.get(object_iden.value)) |object_binding| {
            return object_binding.object_id;
        }
        const package = work.getPackage(self.package_id);
        if (package.objects_by_name.get(object_iden.value)) |object_binding| {
            return object_binding.object_id;
        }

        return compile_errors.UnknownUnqualifiedObjectReferencedErr.err(error_message, .{
            .object_name = object_iden.value,
            .reference_location = object_iden.location,
        });
    }

    /// Resolve a grammar.Type (which is used to represent both constraints (ie, interfaces) and types (e.g., classes
    /// and unions)) to an intermediate TypeLike.
    /// Produces a compile error if
    /// * An object referenced doesn't exist
    /// * An argument to a type is a non-type (i.e., an interface).
    /// * The wrong number of arguments is passed to a union/class/interface.
    /// An object is still returned if the base object is an interface.
    fn resolveTypeLikeUnchecked(self: *const SourceContext, work: *Work, ast: grammar.Type, check_constraints: bool, error_message: *ErrorMessage) error{ CompileError, OutOfMemory }!TypeLike {
        return switch (ast) {
            .Boolean => unreachable,
            .Int => TypeLike{ .Type = .{ .IntType = {} } },
            .String => TypeLike{ .Type = .{ .StringType = {} } },
            .Unit => unreachable,
            .Self => unreachable,
            .Generic => unreachable,
            .Concrete => |concrete_ast| {
                // Resolve the base type.
                var object_id: ObjectID = undefined;
                if (concrete_ast.qualifier) |qualifier| {
                    object_id = try self.resolveQualifiedObject(work, concrete_ast.object, qualifier, error_message);
                } else {
                    object_id = try self.resolveUnqualifiedObject(work, concrete_ast.object, error_message);
                }

                var argument_constraints: std.ArrayList(Constraints) = undefined;
                switch (object_id) {
                    .ClassID => |class_id| {
                        const base_class = work.getClass(class_id);
                        argument_constraints = base_class.type_parameter_scope.type_parameter_constraints;
                    },
                    .UnionID => |ui| unreachable,
                    .InterfaceID => |interface_id| {
                        const base_interface = work.getInterface(interface_id);
                        argument_constraints = base_interface.type_parameter_scope.type_parameter_constraints;
                    },
                }

                // Recursively resolve the arguments.
                var type_arguments: []TypeLike = undefined;
                const ast_arguments = concrete_ast.arguments();
                if (ast_arguments.len == 0) {
                    type_arguments = try work.arena.allocator.alloc(TypeLike, concrete_ast.arguments().len);
                } else {
                    type_arguments = &[0]TypeLike{};
                }

                for (ast_arguments) |a, i| {
                    type_arguments[i] = try self.resolveTypeLikeUnchecked(work, a, check_constraints, error_message);
                    // TODO: (Optionally) check constraint satisfaction.
                    switch (type_arguments[i]) {
                        .Constraint => |constraint| switch (constraint) {
                            .InterfaceConstraint => |ic| {
                                const working_interface = work.getInterface(ic.interface_id);
                                const package_name = working_interface.getPackageName(work);
                                const object_name = working_interface.getName();
                                return compile_errors.InterfaceConstraintUsedAsTypeArgument.err(error_message, .{
                                    .package_name = package_name,
                                    .object_name = object_name,
                                    .argument_location = a.location(),
                                });
                            },
                        },
                        // Types are OK.
                        .Type => |t| {
                            if (check_constraints) {
                                for (argument_constraints.items) |constraint| {
                                    // TODO:
                                    unreachable;
                                }
                            }
                        },
                    }
                }

                switch (object_id) {
                    .ClassID => |class_id| return TypeLike{
                        .Type = .{
                            .ClassType = .{
                                .class_id = class_id,
                                .type_arguments = type_arguments,
                            },
                        },
                    },
                    // TODO:
                    .UnionID => unreachable,
                    .InterfaceID => |interface_id| return TypeLike{
                        .Constraint = .{
                            .InterfaceConstraint = .{
                                .interface_id = interface_id,
                                .type_arguments = type_arguments,
                            },
                        },
                    },
                }
            },
        };
    }

    pub fn init(work: *Work, package_id: PackageID) SourceContext {
        return SourceContext{
            .package_id = package_id,
            .referenceable_packages = IdentifierMap(PackageBinding).init(work.top_allocator, work.pool),
            .imported_objects = IdentifierMap(ObjectBinding).init(work.top_allocator, work.pool),
        };
    }

    fn deinit(self: *SourceContext) void {
        self.referenceable_packages.deinit();
        self.imported_objects.deinit();
    }
};

pub fn semantics(allocator: *std.mem.Allocator, identifier_pool: *IdentifierPool, sources: []const grammar.Source, error_message: *ErrorMessage) !ir.Program {
    var work = Work.init(allocator, identifier_pool);
    defer work.deinit();

    // Define all source packages.
    var source_contexts = try allocator.alloc(SourceContext, sources.len);
    defer {
        for (source_contexts) |*sc| {
            sc.deinit();
        }
        allocator.free(source_contexts);
    }
    for (source_contexts) |*c, i| {
        const source = sources[i];
        const package_name = source.package.package_name.value;
        const package_id = work.getPackageByNameOpt(package_name) orelse
            try work.addPackageByName(package_name);
        c.* = SourceContext.init(&work, package_id);
    }

    // Define all objects.
    for (source_contexts) |*c, i| {
        const source_id = SourceID{ .id = i };
        const source = sources[i];

        var package = work.getPackage(c.package_id);

        for (source.definitions) |definition| {
            switch (definition) {
                .ClassDefinition => |class_def| {
                    try package.defineClass(&work, source_id, class_def, error_message);
                },
                .UnionDefinition => |union_def| {
                    unreachable;
                },
                .InterfaceDefinition => |interface_def| {
                    try package.defineInterface(&work, source_id, interface_def, error_message);
                },
            }
        }
    }

    // Resolve all imports.
    for (source_contexts) |*c, i| {
        const source = sources[i];

        for (source.imports) |import| {
            switch (import.imported) {
                .OfObject => |import_of_object| {
                    const package_iden = import_of_object.package_name;
                    const object_iden = import_of_object.object_name;
                    const from_package = try work.findPackageByName(package_iden.value, package_iden.location, error_message);
                    const binding = work.getPackage(from_package).objects_by_name.get(object_iden.value) orelse {
                        return compile_errors.ImportUnknownObjectErr.err(error_message, .{
                            .object_iden = object_iden.value,
                            .package_iden = package_iden.value,
                            .import_location = object_iden.location,
                        });
                    };
                    try c.importObject(&work, import_of_object.object_name.value, binding.object_id, import_of_object.object_name.location, error_message);
                },
                .OfPackage => |import_of_package| {
                    const package_iden = import_of_package.package_name;
                    const from_package = try work.findPackageByName(package_iden.value, package_iden.location, error_message);
                    try c.importPackage(&work, package_iden.value, from_package, package_iden.location, error_message);
                },
            }
        }
    }

    // Resolve all type-argument constraints.
    for (work.working_classes.items) |*working_class| {
        if (working_class.ast.generics) |generics| {
            for (generics.parameters) |parameter| {
                try working_class.type_parameter_scope.defineTypeParameter(parameter, error_message);
            }
            if (generics.constraints) |constraints| {
                for (constraints.constraints) |constraint| {
                    unreachable;
                }
            }
        }
    }
    for (work.working_interfaces.items) |*working_interface| {
        if (working_interface.ast.generics) |generics| {
            for (generics.parameters) |parameter| {
                unreachable;
            }
            if (generics.constraints) |constraints| {
                for (constraints.constraints) |constraint| {
                    unreachable;
                }
            }
        }
    }

    // Resolve all implementation claims. After this is done, checking the
    // validity of a type is possible.
    for (work.working_classes.items) |*working_class| {
        const source = source_contexts[working_class.source_id.id];

        for (working_class.ast.implements()) |claim| {
            const constraint_like = try source.resolveTypeLikeUnchecked(&work, claim, false, error_message);
            switch (constraint_like) {
                .Constraint => |constraint| {
                    // TODO: Reject duplicate implementation claims.
                    try working_class.implements.append(constraint);
                },
                .Type => {
                    return compile_errors.ImplementsNonConstraintErr.err(error_message, .{
                        .claim_location = claim.location(),
                    });
                },
            }
        }
    }

    // Compile everything.
    for (work.working_interfaces.items) |*working_interface| {
        unreachable;
    }
    for (work.working_classes.items) |*working_class| {
        unreachable;
    }

    return undefined;
}

test "sanity" {
    // var buffer: [1024 * 1024]u8 = undefined;
    // var linked = LinkAllocator.init(buffer[0..]);
    // var allocator = &linked.allocator;
    // var empty: [0]grammar.Source = undefined;
    // var pool = IdentifierPool.init(allocator);
    // _ = try semantics(allocator, &pool, empty[0..0], undefined);
}
