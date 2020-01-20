// semantics.zig:
// Generates IR from ASTs.

const std = @import("std");

const LinkAllocator = @import("linkalloc.zig").LinkAllocator;
const StringTrie = @import("trie.zig").StringTrie;

const grammar = @import("grammar.zig");
const ir = @import("ir.zig");
const Location = grammar.Location;
const ErrorMessage = grammar.ErrorMessage;
const Identifier = @import("identifiers.zig").Identifier;
const IdentifierPool = @import("identifiers.zig").IdentifierPool;
const IdentifierMap = @import("identifiers.zig").IdentifierMap;

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

    /// A pool of Identifiers used in this program.
    identifier_pool: *IdentifierPool,

    /// The set of packages names that have been defined.
    package_set: IdentifierMap(usize),

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

    /// Represents a package (which may be shared between multiple SourceContexts).
    const Package = struct {
        program_context: *ProgramContext,
        name: Identifier,
        definitions: IdentifierMap(Definition),

        fn defineObject(self: *Package, name: grammar.Leaf("TypeIden"), object: ObjectID) !void {
            if (self.definitions.get(name.value)) |previous| {
                self.program_context.error_message.* = (try ErrorBuilder.init(self.program_context.allocator)) //
                    .text("The object `").text(self.name.string()).text(":").text(name.value.string()).text("` is defined for a second time") //
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

        fn lookupObject(self: *Package, name: grammar.Leaf("TypeIden")) !Definition {
            if (self.definitions.get(name.value)) |definition| {
                return definition.*;
            }
            self.program_context.error_message.* = (try ErrorBuilder.init(self.program_context.allocator)) //
                .text("There is no object called `") //
                .text(self.name.string()).text(":").text(name.value.string()) //
                .text("` defined anywhere.") //
                .text("\nHowever, it's referenced").at(name.location) //
                .build();
            return error.CompileError;
        }

        fn defineClass(self: *Package, name: grammar.Leaf("TypeIden"), source: *SourceContext) !void {
            const id = ObjectID{ .Class = self.program_context.vendClassId() };
            try source.definitions.append(id);
            try self.defineObject(name, id);
        }

        fn defineUnion(self: *Package, name: grammar.Leaf("TypeIden"), source: *SourceContext) !void {
            const id = ObjectID{ .Union = self.program_context.vendUnionId() };
            try source.definitions.append(id);
            try self.defineObject(name, id);
        }

        fn defineInterface(self: *Package, name: grammar.Leaf("TypeIden"), source: *SourceContext) !void {
            const id = ObjectID{ .Interface = self.program_context.vendInterfaceId() };
            try source.definitions.append(id);
            try self.defineObject(name, id);
        }
    };

    fn init(allocator: *std.mem.Allocator, identifier_pool: *IdentifierPool, error_message: *ErrorMessage) ProgramContext {
        return ProgramContext{
            .allocator = allocator,
            .identifier_pool = identifier_pool,
            .package_set = IdentifierMap(usize).init(allocator, identifier_pool),
            .packages = std.ArrayList(Package).init(allocator),
            .error_message = error_message,
            .next_class_id = 0,
            .next_union_id = 0,
            .next_interface_id = 0,
        };
    }

    /// Returns a package with the name.
    /// Throws an error if no such package has been defined.
    fn lookupPackage(self: *ProgramContext, name: Identifier, lookup_location: Location) !*Package {
        if (self.package_set.get(name)) |package_index| {
            return &self.packages.toSlice()[package_index.*];
        }

        self.error_message.* = (try ErrorBuilder.init(self.allocator)) //
            .text("There is no package named `") //
            .text(name.string()) //
            .text("`, but it's referenced") //
            .at(lookup_location) //
            .build();
        return error.CompileError;
    }

    /// Defines a package. A package may be safely defined multipled times,
    /// since multiple source files can share a package.
    fn definePackage(self: *ProgramContext, name: Identifier) !*Package {
        const p: *IdentifierMap(usize) = &self.package_set;
        const r: ?*usize = p.get(name);
        if (r) |package_index| {
            return &self.packages.toSlice()[package_index.*];
        }
        const index = self.packages.count();
        try self.packages.append(Package{
            .name = name,
            .program_context = self,
            .definitions = IdentifierMap(Definition).init(self.allocator, self.identifier_pool),
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

    /// The objects defined by this source context.
    definitions: std.ArrayList(ObjectID),

    /// The set of package names that are in-scope for this source.
    const PackageImport = struct {
        package: *ProgramContext.Package,
        location: Location,
    };
    imported_packages: IdentifierMap(PackageImport),

    package: *ProgramContext.Package,

    const ObjectBinding = struct {
        object: ObjectID,
        binding_location: Location,
        sort: enum {
            Import,
            Definition,
        },
    };

    /// The set of object names that are in-scope for this source.
    object_map: IdentifierMap(ObjectBinding),

    /// Create an empty context.
    fn init(program_context: *ProgramContext, package_definition: grammar.PackageDef) !SourceContext {
        var allocator = program_context.allocator;
        const package_name = package_definition.package_name.value;

        // Initialize the object map with the objects defined in the given package.
        var object_map = IdentifierMap(ObjectBinding).init(allocator, program_context.identifier_pool);
        var package = try program_context.definePackage(package_name);
        // TODO: Iterate over package contexts, bringing object names into scope.

        var imported_packages = IdentifierMap(PackageImport).init(allocator, program_context.identifier_pool);

        return SourceContext{
            .definitions = std.ArrayList(ObjectID).init(allocator),
            .program_context = program_context,
            .package = package,
            // TODO: Why does this compile with `STrie(void)`?
            .imported_packages = imported_packages,
            .object_map = object_map,
        };
    }

    fn introduceObject(self: *SourceContext, definition: ProgramContext.Definition) !void {
        return error.TODO;
    }

    fn importObject(self: *SourceContext, import: *const grammar.ImportOfObject) !void {
        const package = try self.program_context.lookupPackage(import.package_name.value, import.package_name.location);
        const definition = try package.lookupObject(import.object_name);
        if (self.object_map.get(import.object_name.value)) |preexisting| {
            // This name is already defined.
            self.program_context.error_message.* = (try ErrorBuilder.init(self.program_context.allocator)) //
                .text("The name `") //
                .text(import.object_name.value.string()) //
                .text("` has already been bound") //
                .at(preexisting.binding_location) //
                .text("However, it's imported again") //
                .at(import.object_name.location) //
                .build();
            return error.CompileError;
        }

        try self.object_map.put(import.object_name.value, ObjectBinding{
            .object = definition.object,
            .binding_location = import.object_name.location,
            .sort = .Import,
        });
    }

    fn importPackage(self: *SourceContext, import: *const grammar.ImportOfPackage) !void {
        const leaf = import.package_name;
        if (leaf.value.eq(self.package.name)) {
            self.program_context.error_message.* = (try ErrorBuilder.init(self.program_context.allocator)) //
                .text("The package `") //
                .text(self.package.name.string()) //
                .text("` cannot import itself.\n") //
                .text("However, it's imported") //
                .at(import.location) //
                .build();
            return error.CompileError;
        }

        var package = try self.program_context.lookupPackage(leaf.value, leaf.location);
        if (self.imported_packages.get(leaf.value)) |present| {
            // Already exists.
            self.program_context.error_message.* = (try ErrorBuilder.init(self.program_context.allocator)) //
                .text("The package `") //
                .text(leaf.value.string()) //
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

pub fn semantics(allocator: *std.mem.Allocator, identifier_pool: *IdentifierPool, sources: []const grammar.Source, error_message: *ErrorMessage) !ir.Program {
    var program_context = ProgramContext.init(allocator, identifier_pool, error_message);

    // Collect the set of packages and definitions.
    var source_contexts = try allocator.alloc(SourceContext, sources.len);
    for (source_contexts) |*ctx, source_index| {
        const source = sources[source_index];

        // Initialize with all of the names from the source's package.
        ctx.* = SourceContext.init(&program_context, source.package);

        for (source.definitions) |definition| {
            var package = try program_context.definePackage(source.package.package_name.value);
            switch (definition) {
                .ClassDefinition => |c| try package.defineClass(c.class_name, ctx),
                .UnionDefinition => |u| try package.defineUnion(u.union_name, ctx),
                .InterfaceDefinition => |i| try package.defineInterface(i.interface_name, ctx),
            }
        }
    }

    // Create the source context for each scope.
    for (source_contexts) |*ctx, source_index| {
        const source = sources[source_index];

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

        // Bring into scope all the objects defined by the package.
        //source.package.definitions;
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
