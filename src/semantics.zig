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

const WorkingPackage = struct {
    /// The index into the `working_packages` array of `Work`.
    id: usize,

    pub fn init(id: usize) WorkingPackage {
        return WorkingPackage{ .id = id };
    }
};

const WorkingClass = struct {
    /// The index into the `working_classes` array of `Work`.
    id: usize,

    /// The index of the containing package in the `working_packages` array of `Work`.
    package_id: usize,

    ast: grammar.ClassDefinition,
};

const WorkingFunction = struct {
    /// The index into the `working_functions` array of `Work`.
    id: usize,

    ast: grammar.FunctionDef,
};

const PackageID = struct { id: usize };

const Work = struct {
    allocator: *std.mem.Allocator,
    pool: *IdentifierPool,

    working_packages: std.ArrayList(WorkingPackage),
    working_classes: std.ArrayList(WorkingClass),
    working_functions: std.ArrayList(WorkingFunction),

    package_ids_by_name: IdentifierMap(usize),

    fn getPackage(self: *Work, package_id: PackageID) *WorkingPackage {
        return &self.working_packages.items[package_id.id];
    }

    pub fn getPackageByName(self: *Work, package_name: Identifier) ?PackageID {
        if (self.package_ids_by_name.get(package_name)) |id| {
            return PackageID{ .id = id.* };
        }
        return null;
    }

    pub fn addPackageByName(self: *Work, package_name: Identifier) !PackageID {
        assert(self.getPackageByName(package_name) == null);

        const new_id = self.working_packages.items.len;
        const package = WorkingPackage.init(new_id);
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

            .package_ids_by_name = IdentifierMap(usize).init(allocator, identifier_pool),
        };
    }
};

const SourceContext = struct {
    referenceable_packages: IdentifierMap(PackageID),

    package_id: PackageID,

    pub fn init(work: *Work, package_id: PackageID) SourceContext {
        return SourceContext{
            .package_id = package_id,
            .referenceable_packages = IdentifierMap(PackageID).init(work.allocator, work.pool),
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
        const package_id = if (work.getPackageByName(package_name)) |id| id else try work.addPackageByName(package_name);
        c.* = SourceContext.init(&work, package_id);
    }

    // Define all objects.
    for (source_contexts) |*c, i| {
        const source = sources[i];

        var package = work.getPackage(c.package_id);

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

    // Resolve all imports.
    for (source_contexts) |*c, i| {
        const source = sources[i];

        for (source.imports) |import| {
            unreachable;
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
    var buffer: [1024 * 1024]u8 = undefined;
    var linked = LinkAllocator.init(buffer[0..]);
    var allocator = &linked.allocator;
    var empty: [0]grammar.Source = undefined;
    var pool = IdentifierPool.init(allocator);
    _ = try semantics(allocator, &pool, empty[0..0], undefined);
}
