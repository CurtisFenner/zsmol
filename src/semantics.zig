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
            .objects_by_name = IdentifierMap(ObjectBinding).init(work.allocator, work.pool),
        };
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

const WorkingClass = struct {
    /// The index into the `working_classes` array of `Work`.
    id: usize,

    /// The index of the containing package in the `working_packages` array of `Work`.
    package_id: PackageID,

    /// The index of the defining source file.
    source_id: SourceID,

    ast: *const grammar.ClassDefinition,
};

const WorkingInterface = struct {
    /// The index into the `working_interfaces` array of `Work`.
    id: usize,

    /// The index of the containing package in the `working_packages` array of `Work`.
    package_id: PackageID,

    /// The index of the defining source file.
    source_id: SourceID,

    ast: *const grammar.InterfaceDefinition,
};

const WorkingFunction = struct {
    /// The index into the `working_functions` array of `Work`.
    id: usize,

    ast: grammar.FunctionDef,
};

const SourceID = struct { id: usize };
const ClassID = struct { id: usize };
const UnionID = struct { id: usize };
const InterfaceID = struct { id: usize };
const PackageID = struct { id: usize };

const Work = struct {
    allocator: *std.mem.Allocator,
    pool: *IdentifierPool,

    working_packages: std.ArrayList(WorkingPackage),
    working_classes: std.ArrayList(WorkingClass),
    working_interfaces: std.ArrayList(WorkingInterface),
    working_functions: std.ArrayList(WorkingFunction),

    package_ids_by_name: IdentifierMap(usize),

    fn getPackage(self: *Work, package_id: PackageID) *WorkingPackage {
        return &self.working_packages.items[package_id.id];
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
        try self.working_classes.append(WorkingClass{
            .id = self.working_classes.items.len,
            .package_id = package_id,
            .source_id = source_id,
            .ast = ast,
        });
        return id;
    }
    fn addInterface(self: *Work, package_id: PackageID, source_id: SourceID, ast: *const grammar.InterfaceDefinition) !InterfaceID {
        const id = InterfaceID{ .id = self.working_interfaces.items.len };
        try self.working_interfaces.append(WorkingInterface{
            .id = self.working_interfaces.items.len,
            .package_id = package_id,
            .source_id = source_id,
            .ast = ast,
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

    pub fn init(allocator: *std.mem.Allocator, identifier_pool: *IdentifierPool) Work {
        return Work{
            .allocator = allocator,
            .pool = identifier_pool,

            .working_packages = std.ArrayList(WorkingPackage).init(allocator),
            .working_classes = std.ArrayList(WorkingClass).init(allocator),
            .working_functions = std.ArrayList(WorkingFunction).init(allocator),
            .working_interfaces = std.ArrayList(WorkingInterface).init(allocator),

            .package_ids_by_name = IdentifierMap(usize).init(allocator, identifier_pool),
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

    pub fn init(work: *Work, package_id: PackageID) SourceContext {
        return SourceContext{
            .package_id = package_id,
            .referenceable_packages = IdentifierMap(PackageBinding).init(work.allocator, work.pool),
            .imported_objects = IdentifierMap(ObjectBinding).init(work.allocator, work.pool),
        };
    }
};

pub fn semantics(allocator: *std.mem.Allocator, identifier_pool: *IdentifierPool, sources: []const grammar.Source, error_message: *ErrorMessage) !ir.Program {
    var work = Work.init(allocator, identifier_pool);

    // Define all source packages.
    var source_contexts = try allocator.alloc(SourceContext, sources.len);
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

    // Resolve all implementation claims.
    for (source_contexts) |*c, i| {
        const source = sources[i];

        for (source.definitions) |definition| {
            switch (definition) {
                .ClassDefinition => |cd| {
                    unreachable;
                },
                .UnionDefinition => |ud| {
                    unreachable;
                },
                .InterfaceDefinition => |id| {
                    unreachable;
                },
            }
        }
    }

    // Build a type-checker for each source context.
    // Compile pre/post conditions.
    for (source_contexts) |*c, i| {
        const source = sources[i];

        for (source.definitions) |definition| {
            switch (definition) {
                .ClassDefinition => |cd| {
                    unreachable;
                },
                .UnionDefinition => |ud| {
                    unreachable;
                },
                .InterfaceDefinition => |id| {
                    unreachable;
                },
            }
        }
    }

    // Compile everything using pre/post condition blocks.
    for (source_contexts) |*c, i| {
        const source = sources[i];

        for (source.definitions) |definition| {
            switch (definition) {
                .ClassDefinition => |cd| {
                    unreachable;
                },
                .UnionDefinition => |ud| {
                    unreachable;
                },
                .InterfaceDefinition => |id| {
                    unreachable;
                },
            }
        }
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
