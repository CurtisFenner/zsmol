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

    pub fn init() WorkingPackage {
        return WorkingPackage{};
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

const Work = struct {
    working_packages: std.ArrayList(WorkingPackage),
    working_classes: std.ArrayList(WorkingClass),
    working_functions: std.ArrayList(WorkingFunction),

    package_ids_by_name: IdentifierMap(usize),

    pub fn getOrAddPackage(self: *Work, package_name: Identifier) !usize {
        if (package_ids_by_name.get(package_name)) |id| {
            return id;
        }
        const package = WorkingPackage.init();
        const new_id = self.working_packages.count();
        try self.working_packages.append(package);
        try self.package_ids_by_name.put(package_name, new_id);
        return new_id;
    }

    pub fn init(allocator: *std.mem.Allocator, identifier_pool: *IdentifierPool) Work {
        return Work{
            .working_packages = std.ArrayList(WorkingPackage).init(allocator),
            .working_classes = std.ArrayList(WorkingClass).init(allocator),
            .working_functions = std.ArrayList(WorkingFunction).init(allocator),

            .package_ids_by_name = IdentifierMap(usize).init(allocator, identifier_pool),
        };
    }
};

pub fn semantics(allocator: *std.mem.Allocator, identifier_pool: *IdentifierPool, sources: []const grammar.Source, error_message: *ErrorMessage) !ir.Program {
    var work = Work.init(allocator, identifier_pool);
    var x = try allocator.alloc(u8, 1);
    unreachable;
}

test "sanity" {
    var buffer: [1024 * 1024]u8 = undefined;
    var linked = LinkAllocator.init(buffer[0..]);
    var allocator = &linked.allocator;
    var empty: [0]grammar.Source = undefined;
    _ = try semantics(allocator, empty[0..0], undefined);
}
