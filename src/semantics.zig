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

    // TODO: These will become lists containing the actual metadata (fields, arity, etc)
    next_class_id: usize,
    next_union_id: usize,
    next_interface_id: usize,

    /// The set of all package definitions
    packages: IdentifierMap(Package),

    /// An error message to return.
    error_message: *ErrorMessage,

    const Definition = struct {
        identifier: Identifier,
        binding_location: Location,
        entire_location: Location,
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
                    .at(previous.binding_location) //
                    .build();
                return error.CompileError;
            }

            try self.definitions.put(name.value, Definition{
                .identifier = name.value,
                .binding_location = name.location,
                // TODO:
                .entire_location = undefined,
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
    };

    fn init(allocator: *std.mem.Allocator, identifier_pool: *IdentifierPool, error_message: *ErrorMessage) ProgramContext {
        return ProgramContext{
            .allocator = allocator,
            .identifier_pool = identifier_pool,
            .packages = IdentifierMap(Package).init(allocator, identifier_pool),
            .error_message = error_message,
            .next_class_id = 0,
            .next_union_id = 0,
            .next_interface_id = 0,
        };
    }

    /// Returns a package with the name.
    /// Throws a compilation error if no such package has been defined.
    fn lookupPackage(self: *ProgramContext, name: Identifier, lookup_location: Location) !*Package {
        if (self.packages.get(name)) |p| {
            return p;
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
    fn definePackage(self: *ProgramContext, name: Identifier) !void {
        if (self.packages.get(name) != null) {
            return;
        }

        try self.packages.put(name, Package{
            .name = name,
            .program_context = self,
            .definitions = IdentifierMap(Definition).init(self.allocator, self.identifier_pool),
        });
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
        package: Identifier,
        location: Location,
    };
    imported_packages: IdentifierMap(PackageImport),

    package: Identifier,

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
    fn init(program_context: *ProgramContext, package_identifier: Identifier) !SourceContext {
        var allocator = program_context.allocator;

        // Initialize the object map with the objects defined in the given package.
        var object_map = IdentifierMap(ObjectBinding).init(allocator, program_context.identifier_pool);
        try program_context.definePackage(package_identifier);
        // TODO: Iterate over package contexts, bringing object names into scope.

        var imported_packages = IdentifierMap(PackageImport).init(allocator, program_context.identifier_pool);

        return SourceContext{
            .definitions = std.ArrayList(ObjectID).init(allocator),
            .program_context = program_context,
            .package = package_identifier,
            .imported_packages = imported_packages,
            .object_map = object_map,
        };
    }

    fn defineClass(self: *SourceContext, name: grammar.Leaf("TypeIden")) !void {
        const id = ObjectID{ .Class = self.program_context.vendClassId() };
        try self.program_context.packages.get(self.package).?.defineObject(name, id);
    }

    fn defineUnion(self: *SourceContext, name: grammar.Leaf("TypeIden")) !void {
        const id = ObjectID{ .Union = self.program_context.vendUnionId() };
        try self.program_context.packages.get(self.package).?.defineObject(name, id);
    }

    fn defineInterface(self: *SourceContext, name: grammar.Leaf("TypeIden")) !void {
        const id = ObjectID{ .Interface = self.program_context.vendInterfaceId() };
        try self.program_context.packages.get(self.package).?.defineObject(name, id);
    }

    fn introduceObject(self: *SourceContext, definition: ProgramContext.Definition) !void {
        if (self.object_map.get(definition.identifier)) |preexisting| {
            // This name is already defined.
            self.program_context.error_message.* = (try ErrorBuilder.init(self.program_context.allocator)) //
                .text("The name `") //
                .text(definition.identifier.string()) //
                .text("` has already been bound") //
                .at(preexisting.binding_location) //
                .text("However, it's defined again") //
                .at(definition.binding_location) //
                .build();
            return error.CompileError;
        }

        try self.object_map.put(definition.identifier, ObjectBinding{
            .object = definition.object,
            .binding_location = definition.binding_location,
            .sort = .Definition,
        });
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
        const package_name = import.package_name.value;
        if (package_name.eq(self.package)) {
            self.program_context.error_message.* = (try ErrorBuilder.init(self.program_context.allocator)) //
                .text("The package `") //
                .text(self.package.string()) //
                .text("` cannot import itself.\n") //
                .text("However, it's imported") //
                .at(import.location) //
                .build();
            return error.CompileError;
        }

        var package = try self.program_context.lookupPackage(package_name, import.package_name.location);
        if (self.imported_packages.get(package_name)) |present| {
            // Already exists.
            self.program_context.error_message.* = (try ErrorBuilder.init(self.program_context.allocator)) //
                .text("The package `") //
                .text(package_name.string()) //
                .text("` has already been imported") //
                .at(present.location) //
                .text("but you try to import it again") //
                .at(import.location) //
                .build();
            return error.CompileError;
        }
        try self.imported_packages.put(package_name, PackageImport{
            .package = package_name,
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
        try program_context.definePackage(source.package.package_name.value);
        ctx.* = SourceContext.init(&program_context, source.package.package_name.value);

        for (source.definitions) |definition| {
            switch (definition) {
                .ClassDefinition => |c| try ctx.defineClass(c.class_name),
                .UnionDefinition => |u| try ctx.defineUnion(u.union_name),
                .InterfaceDefinition => |i| try ctx.defineInterface(i.interface_name),
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
        var it = program_context.packages.get(ctx.package).?.definitions.values();
        while (it.next()) |definition| {
            try ctx.introduceObject(definition);
        }
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
