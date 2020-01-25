const std = @import("std");
const assert = std.debug.assert;

const LinkAllocator = @import("linkalloc.zig").LinkAllocator;

pub fn NibbleTrie(comptime Value: type) type {
    return struct {
        const Self = @This();

        const Block = struct {
            value: ?Value,
            branches: [16]?usize,

            fn empty() Block {
                return Block{
                    .value = null,
                    .branches = [_]?usize{null} ** 16,
                };
            }
        };

        blocks: std.ArrayList(Block),

        pub const ValueIterator = struct {
            trie: *Self,
            index: usize,

            pub fn next(self: *ValueIterator) ?Value {
                while (true) {
                    if (self.index >= self.trie.blocks.count()) {
                        return null;
                    }
                    const at = self.index;
                    self.index += 1;
                    if (self.trie.blocks.toSlice()[at].value) |v| {
                        return v;
                    }
                }
            }
        };

        pub fn values(self: *Self) ValueIterator {
            return ValueIterator{
                .trie = self,
                .index = 0,
            };
        }

        /// Creates an empty trie.
        pub fn init(allocator: *std.mem.Allocator) Self {
            return Self{
                .blocks = std.ArrayList(Block).init(allocator),
            };
        }

        /// Frees all of the internal memory owned by this trie.
        pub fn deinit(self: *Self) void {
            self.blocks.deinit();
        }

        /// Puts a value into the trie, replacing any value that was previously
        /// present.
        pub fn put(self: *Self, key: var, value: Value) !void {
            if (self.blocks.count() == 0) {
                try self.blocks.append(Block.empty());
            }
            var index: usize = 0;
            while (key.next()) |nibble| {
                var block: *Block = &self.blocks.toSlice()[index];
                if (block.branches[nibble]) |next_index| {
                    index = next_index;
                } else {
                    try self.blocks.append(Block.empty());
                    block = &self.blocks.toSlice()[index];
                    const new_index = self.blocks.count() - 1;
                    block.branches[nibble] = new_index;
                    index = new_index;
                }
            }
            var block = &self.blocks.toSlice()[index];
            block.value = value;
        }

        /// Gets the most recently put value associated with the key.
        pub fn get(self: *const Self, key: var) ?*Value {
            if (self.blocks.count() == 0) {
                return null;
            }

            var index: usize = 0;
            while (key.next()) |nibble| {
                const block = self.blocks.toSlice()[index];
                if (block.branches[nibble]) |next_index| {
                    index = next_index;
                } else {
                    return null;
                }
            }

            if (self.blocks.toSlice()[index].value) |*value| {
                return value;
            } else {
                return null;
            }
        }
    };
}

pub const NibbleIterator = struct {
    string: []const u8,
    index: usize,

    pub fn init(string: []const u8) NibbleIterator {
        return NibbleIterator{
            .string = string,
            .index = 0,
        };
    }

    pub fn next(self: *NibbleIterator) ?u8 {
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

pub fn StringTrie(comptime Value: type) type {
    return struct {
        const Self = @This();

        nibble_trie: NibbleTrie(Value),

        pub fn init(allocator: *std.mem.Allocator) Self {
            return Self{
                .nibble_trie = NibbleTrie(Value).init(allocator),
            };
        }

        pub fn deinit(self: *Self) void {
            self.nibble_trie.deinit();
        }

        pub fn get(self: *const Self, key: []const u8) ?*Value {
            var iterator = NibbleIterator.init(key);
            return self.nibble_trie.get(&iterator);
        }

        pub fn put(self: *Self, key: []const u8, value: Value) !void {
            var iterator = NibbleIterator.init(key);
            return self.nibble_trie.put(&iterator, value);
        }
    };
}

test "NibbleTrie simple" {
    var buffer: [99000]u8 = undefined;
    var linked = LinkAllocator.init(buffer[0..]);
    defer assert(linked.isEmpty());
    var allocator = &linked.allocator;
    var trie = StringTrie(u8).init(allocator);
    defer trie.deinit();

    assert(trie.get("hi") == null);
    try trie.put("abc", 7);

    assert(trie.get("abc").?.* == 7);

    try trie.put("ab", 6);
    assert(trie.get("ab").?.* == 6);
    assert(trie.get("abc").?.* == 7);

    try trie.put("abaa", 5);
    assert(trie.get("abaa").?.* == 5);
    assert(trie.get("ab").?.* == 6);
    assert(trie.get("abc").?.* == 7);
    assert(trie.get("abcd") == null);

    var it = trie.nibble_trie.values();
    assert(it.next().? == 6);
    assert(it.next().? == 7);
    assert(it.next().? == 5);
    assert(it.next() == null);
}
