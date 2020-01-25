const std = @import("std");
const assert = std.debug.assert;

const StringTrie = @import("trie.zig").StringTrie;
const NibbleIterator = @import("trie.zig").NibbleIterator;
const NibbleTrie = @import("trie.zig").NibbleTrie;
const LinkAllocator = @import("linkalloc.zig").LinkAllocator;

pub const IdentifierPool = struct {
    pool: StringTrie(u32),
    sources: std.ArrayList([]const u8),

    /// The `string` must outlive this pool.
    pub fn add(self: *IdentifierPool, string: []const u8) !Identifier {
        if (self.pool.get(string)) |id| {
            return Identifier{ .pool = self, .id = id.* };
        } else {
            const vended = @intCast(u32, self.sources.count());
            try self.pool.put(string, vended);
            try self.sources.append(string);
            return Identifier{ .pool = self, .id = vended };
        }
    }

    pub fn get(self: *const IdentifierPool, string: []const u8) ?Identifier {
        if (self.pool.get(string)) |id| {
            return Identifier{ .pool = self, .id = id.* };
        }
        return null;
    }

    pub fn init(allocator: *std.mem.Allocator) IdentifierPool {
        return IdentifierPool{
            .pool = StringTrie(u32).init(allocator),
            .sources = std.ArrayList([]const u8).init(allocator),
        };
    }

    pub fn deinit(self: *IdentifierPool) void {
        self.pool.deinit();
        self.sources.deinit();
    }
};

pub const Identifier = struct {
    pool: *const IdentifierPool,
    id: u32,

    pub fn eq(self: Identifier, other: Identifier) bool {
        assert(self.pool == other.pool);
        return self.id == other.id;
    }

    pub fn string(self: *const Identifier) []const u8 {
        return self.pool.sources.toSlice()[self.id];
    }
};

test "simple" {
    var buffer: [30000]u8 = undefined;
    var linked = LinkAllocator.init(buffer[0..]);
    defer assert(linked.isEmpty());
    var allocator = &linked.allocator;

    var pool = IdentifierPool.init(allocator);
    defer pool.deinit();
    const alpha_1 = try pool.add("alpha");
    const alpha_2 = try pool.add("alpha");
    const beta_1 = try pool.add("beta");
    const gamma_1 = try pool.add("gamma");
    const beta_2 = try pool.add("beta");
    const alpha_3 = try pool.add("alpha");
    const gamma_2 = try pool.add("gamma");

    assert(alpha_1.eq(alpha_2));
    assert(alpha_2.eq(alpha_3));
    assert(alpha_1.eq(alpha_3));
    assert(beta_1.eq(beta_2));
    assert(gamma_1.eq(gamma_2));
    assert(!alpha_1.eq(beta_1));
    assert(!alpha_1.eq(beta_2));
    assert(!alpha_1.eq(gamma_1));
    assert(!alpha_1.eq(gamma_2));
    assert(!alpha_1.eq(beta_1));
    assert(!alpha_3.eq(beta_2));
    assert(!alpha_3.eq(gamma_1));
    assert(!alpha_3.eq(gamma_2));
}

pub const IntIterator = struct {
    string: [4]u8,
    index: usize,

    pub fn init(number: u32) IntIterator {
        var string: [4]u8 = undefined;
        std.mem.writeIntNative(u32, &string, number);
        return IntIterator{
            .string = string,
            .index = 0,
        };
    }

    pub fn next(self: *IntIterator) ?u8 {
        const char_index = self.index / 2;
        if (char_index >= self.string.len) {
            return null;
        }
        const char = self.string[char_index];
        if (self.index % 2 == 0) {
            self.index += 1;
            return char % 16;
        } else {
            self.index += 1;
            return char / 16;
        }
    }
};

pub fn IdentifierMap(comptime Value: type) type {
    return struct {
        identifier_pool: *IdentifierPool,
        nibble_trie: NibbleTrie(Value),

        const Self = @This();

        pub fn init(allocator: *std.mem.Allocator, identifier_pool: *IdentifierPool) Self {
            return Self{
                .identifier_pool = identifier_pool,
                .nibble_trie = NibbleTrie(Value).init(allocator),
            };
        }

        pub fn get(self: *const Self, key: Identifier) ?*Value {
            assert(key.pool == self.identifier_pool);
            var iterator = IntIterator.init(key.id);
            return self.nibble_trie.get(&iterator);
        }

        pub fn put(self: *Self, key: Identifier, value: Value) !void {
            assert(key.pool == self.identifier_pool);
            var iterator = IntIterator.init(key.id);
            return self.nibble_trie.put(&iterator, value);
        }

        pub fn values(self: *Self) NibbleTrie(Value).ValueIterator {
            return self.nibble_trie.values();
        }
    };
}
