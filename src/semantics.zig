// semantics.zig:
// Generates IR from ASTs.

const std = @import("std");

const LinkAllocator = @import("linkalloc.zig").LinkAllocator;
const STrie = @import("strie.zig").STrie;

const grammar = @import("grammar.zig");
const ir = @import("ir.zig");
const Location = grammar.Location;
const ErrorMessage = grammar.ErrorMessage;

const ObjectID = union(enum) {
    Class: usize,
    Union: usize,
    Interface: usize,
};

const ErrorBuilder = struct {
    entries: []ErrorMessage.Entry,
    offset: usize,

    fn init(allocator: *std.mem.Allocator) !ErrorBuilder {
        return ErrorBuilder{
            .entries = try allocator.alloc(ErrorMessage.Entry, 10),
            .offset = 0,
        };
    }

    fn text(self: *ErrorBuilder, str: []const u8) *ErrorBuilder {
        self.entries[self.offset] = ErrorMessage.Entry{
            .Text = str,
        };
        self.offset += 1;
        return self;
    }

    fn at(self: *ErrorBuilder, location: Location) *ErrorBuilder {
        self.entries[self.offset] = ErrorMessage.Entry{
            .AtLocation = location,
        };
        self.offset += 1;
        return self;
    }

    fn build(self: *const ErrorBuilder) ErrorMessage {
        // TODO: Can this be freed safely?
        const out = ErrorMessage{ .entries = self.entries[0..self.offset] };
        return out;
    }
};

/// A context for compiling an entire Smol program.
const ProgramContext = struct {
    allocator: *std.mem.Allocator,

    /// The set of packages names that have been defined.
    package_set: STrie(usize),

    // TODO: These will become lists containing the actual metadata (fields, arity, etc)
    next_class_id: usize,
    next_union_id: usize,
    next_interface_id: usize,

    /// The sequence of package definitions
    packages: std.ArrayList(Package),

    /// An error message to return.
    error_message: *ErrorMessage,

    const Definition = struct {
        location: Location,
        object: ObjectID,
    };

    fn vendClassId(self: *ProgramContext) usize {
        const id = self.next_class_id;
        self.next_class_id += 1;
        return id;
    }
    fn vendUnionId(self: *ProgramContext) usize {
        const id = self.next_union_id;
        self.next_union_id += 1;
        return id;
    }
    fn vendInterfaceId(self: *ProgramContext) usize {
        const id = self.next_interface_id;
        self.next_interface_id += 1;
        return id;
    }

    const Package = struct {
        program_context: *ProgramContext,
        name: []const u8,
        definitions: STrie(Definition),

        fn defineObject(self: *Package, name: grammar.Leaf("TypeIden"), object: ObjectID) !void {
            if (self.definitions.get(name.value)) |previous| {
                self.program_context.error_message.* = (try ErrorBuilder.init(self.program_context.allocator)) //
                    .text("The object `").text(self.name).text(":").text(name.value).text("` is defined for a second time") //
                    .at(name.location) //
                    .text("The first definition was") //
                    .at(previous.location) //
                    .build();
                return error.CompileError;
            }

            try self.definitions.put(name.value, Definition{
                .location = name.location,
                .object = object,
            });
        }

        fn defineClass(self: *Package, name: grammar.Leaf("TypeIden")) !void {
            try self.defineObject(name, ObjectID{ .Class = self.program_context.vendClassId() });
        }

        fn defineUnion(self: *Package, name: grammar.Leaf("TypeIden")) !void {
            try self.defineObject(name, ObjectID{ .Class = self.program_context.vendUnionId() });
        }

        fn defineInterface(self: *Package, name: grammar.Leaf("TypeIden")) !void {
            try self.defineObject(name, ObjectID{ .Class = self.program_context.vendInterfaceId() });
        }
    };

    fn init(allocator: *std.mem.Allocator, error_message: *ErrorMessage) ProgramContext {
        return ProgramContext{
            .allocator = allocator,
            .package_set = STrie(usize).init(allocator),
            .packages = std.ArrayList(Package).init(allocator),
            .error_message = error_message,
            .next_class_id = 0,
            .next_union_id = 0,
            .next_interface_id = 0,
        };
    }

    /// Returns a package with the name.
    /// Throws an error if no such package has been defined.
    fn lookupPackage(self: *ProgramContext, name: []const u8, lookup_location: Location) !*Package {
        if (self.package_set.get(name)) |package_index| {
            return &self.packages.toSlice()[package_index.*];
        }

        self.error_message.* = (try ErrorBuilder.init(self.allocator)) //
            .text("There is no package named `") //
            .text(name) //
            .text("`, but it's referenced") //
            .at(lookup_location) //
            .build();
        return error.CompileError;
    }

    /// Defines a package. A package may be safely defined multipled times,
    /// since multiple source files can share a package.
    fn definePackage(self: *ProgramContext, name: []const u8) !*Package {
        if (self.package_set.get(name)) |package_index| {
            return &self.packages.toSlice()[package_index.*];
        }
        const index = self.packages.count();
        try self.packages.append(Package{
            .name = name,
            .program_context = self,
            .definitions = STrie(Definition).init(self.allocator),
        });
        errdefer _ = self.packages.pop();
        try self.package_set.put(name, index);
        return &self.packages.toSlice()[index];
    }
};

/// A context for compiling a single Smol source file.
const SourceContext = struct {
    /// The context for the program this source file is a part of.
    program_context: *ProgramContext,

    /// The set of package names that are in-scope for this source.
    const PackageImport = struct {
        package: *ProgramContext.Package,
        location: Location,
    };
    imported_packages: STrie(PackageImport),

    package: *ProgramContext.Package,

    const ObjectBinding = struct {
        object: ObjectID,
        location: Location,
        sort: enum {
            Import,
            Definition,
        },
    };

    /// The set of object names that are in-scope for this source.
    object_map: STrie(ObjectBinding),

    /// Create an empty context.
    fn init(program_context: *ProgramContext, package_definition: grammar.PackageDef) !SourceContext {
        var allocator = program_context.allocator;
        const package_name = package_definition.package_name.value;

        // Initialize the object map with the objects defined in the given package.
        var object_map = STrie(ObjectBinding).init(allocator);
        var package = try program_context.definePackage(package_name);
        // TODO: Iterate over package contexts, bringing object names into scope.

        var imported_packages = STrie(PackageImport).init(allocator);
        try imported_packages.put(package_name, PackageImport{
            .package = package,
            .location = package_definition.location,
        });

        return SourceContext{
            .program_context = program_context,
            .package = package,
            // TODO: Why does this compile with `STrie(void)`?
            .imported_packages = imported_packages,
            .object_map = object_map,
        };
    }

    fn importObject(self: *SourceContext, import: *const grammar.ImportOfObject) !void {
        return error.Unimplemented;
    }

    fn importPackage(self: *SourceContext, import: *const grammar.ImportOfPackage) !void {
        const leaf = import.package_name;
        var package = try self.program_context.lookupPackage(leaf.value, leaf.location);
        if (self.imported_packages.get(leaf.value)) |present| {
            // Already exists.
            self.program_context.error_message.* = (try ErrorBuilder.init(self.program_context.allocator)) //
                .text("The package `") //
                .text(leaf.value) //
                .text("` has already been imported") //
                .at(present.location) //
                .text("but you try to import it again") //
                .at(import.location) //
                .build();
            return error.CompileError;
        }
        try self.imported_packages.put(leaf.value, PackageImport{
            .package = package,
            .location = import.location,
        });
    }
};

fn validateArity(program_context: *ProgramContext, generics_opt: ?*const grammar.Generics) !usize {
    if (generics_opt == null) return 0;
    const generics = generics_opt.?.*;
}

pub fn semantics(allocator: *std.mem.Allocator, sources: []const grammar.Source, error_message: *ErrorMessage) !ir.Program {
    var program_context = ProgramContext.init(allocator, error_message);

    // Collect the set of packages and definitions.
    var source_contexts = try allocator.alloc(SourceContext, sources.len);
    for (sources) |source, source_index| {
        for (source.definitions) |definition| {
            var package = try program_context.definePackage(source.package.package_name.value);
            switch (definition) {
                .ClassDefinition => |c| try package.defineClass(c.class_name),
                .UnionDefinition => |u| try package.defineUnion(u.union_name),
                .InterfaceDefinition => |i| try package.defineInterface(i.interface_name),
            }
        }
    }

    // Create the source context for each scope.
    for (source_contexts) |*ctx, source_index| {
        const source = sources[source_index];

        // Initialize with all of the names from the source's package.
        ctx.* = SourceContext.init(&program_context, source.package);

        // Import packages and objects.
        for (source.imports) |import| {
            switch (import.imported) {
                .OfObject => |object| {
                    try ctx.importObject(object);
                },
                .OfPackage => |package| {
                    try ctx.importPackage(package);
                },
            }
        }
    }

    // Collect the set of definitions and signatures.
    for (source_contexts) |*ctx| {}

    // Verify that the signatures are well formed.
    //
    return error.TODO;
}

test "sanity" {
    var buffer: [1024 * 1024]u8 = undefined;
    var linked = LinkAllocator.init(buffer[0..]);
    var allocator = &linked.allocator;
    var empty: [0]grammar.Source = undefined;
    _ = try semantics(allocator, empty[0..0], undefined);
}
