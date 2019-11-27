// strie.zig:
// A trie with string keys.

const std = @import("std");
const assert = std.debug.assert;

const LinkAllocator = @import("linkalloc.zig").LinkAllocator;

/// A trie data structure.
pub fn STrie(comptime Value: type) type {
    return struct {
        const Self = @This();
        // TODO(#2746): Remove this wrapper.
        const Wrap = struct {
            wrapped: Self,
        };
        allocator: *std.mem.Allocator,
        leafs: [16]?Value,
        branches: [16]?*Wrap,

        /// Creates an empty trie.
        pub fn init(allocator: *std.mem.Allocator) Self {
            return Self{
                .allocator = allocator,
                .leafs = [_]?Value{null} ** 16,
                .branches = [_]?*Wrap{null} ** 16,
            };
        }

        /// Frees all of the internal memory owned by this trie.
        pub fn deinit(self: *Self) void {
            for (self.branches) |b| {
                if (b) |branch| {
                    branch.wrapped.deinit();
                    self.allocator.destroy(branch);
                }
            }
        }

        /// Puts a value into the trie, replacing any value that was present.
        pub fn put(self: *Self, key: []const u8, value: Value) error{OutOfMemory}!void {
            assert(key.len != 0);
            const i = key[0];
            const i_lo = i & 0b00001111;
            const i_hi = (i & 0b11110000) >> 4;
            if (self.branches[i_hi] == null) {
                var ptr = try self.allocator.create(Wrap);
                ptr.wrapped = Self.init(self.allocator);
                self.branches[i_hi] = ptr;
            }

            if (key.len == 1) {
                self.branches[i_hi].?.wrapped.leafs[i_lo] = value;
            } else {
                if (self.branches[i_hi].?.wrapped.branches[i_lo] == null) {
                    var ptr = try self.allocator.create(Wrap);
                    ptr.wrapped = Self.init(self.allocator);
                    self.branches[i_hi].?.wrapped.branches[i_lo] = ptr;
                }
                try self.branches[i_hi].?.wrapped.branches[i_lo].?.wrapped.put(key[1..], value);
            }
        }

        /// Gets the most recently put value associated with the key.
        pub fn get(self: *Self, key: []const u8) ?*Value {
            assert(key.len != 0);
            const i = key[0];
            const i_lo = i & 0b00001111;
            const i_hi = (i & 0b11110000) >> 4;
            if (self.branches[i_hi]) |b_hi| {
                if (key.len == 1) {
                    if (b_hi.wrapped.leafs[i_lo]) |*leaf| {
                        return leaf;
                    }
                    return null;
                } else {
                    if (b_hi.wrapped.branches[i_lo]) |b| {
                        return b.wrapped.get(key[1..]);
                    }
                    return null;
                }
            }
            return null;
        }

        /// RETURNS whether or not this trie contains a key which is a
        /// subsequence of the given argument.
        pub fn containsSubsequenceKey(self: *Self, key: []const u8) bool {
            if (key.len == 0) return false;
            for (key) |c, i| {
                const c_lo = c & 0b00001111;
                const c_hi = (c & 0b11110000) >> 4;
                if (self.branches[c_hi]) |b_hi| {
                    if (b_hi.wrapped.leafs[c_lo]) |_| return true;
                    if (b_hi.wrapped.branches[c_lo]) |b_lo| {
                        if (b_lo.wrapped.containsSubsequenceKey(key[i + 1 ..])) return true;
                    }
                }
            }
            return false;
        }
    };
}

test "STrie simple" {
    var buffer: [99000]u8 = undefined;
    var linked = LinkAllocator.init(buffer[0..]);
    defer assert(linked.isEmpty());
    var allocator = &linked.allocator;
    var trie = STrie(u8).init(allocator);
    defer trie.deinit();
    assert(trie.get("hi") == null);
    try trie.put("hello", 7);
    assert(trie.get("hello").?.* == 7);
    assert(trie.get("hellp") == null);
    assert(trie.get("hellop") == null);

    try trie.put("cat", 1);
    assert(trie.containsSubsequenceKey("cat"));
    assert(!trie.containsSubsequenceKey("ct"));
    assert(!trie.containsSubsequenceKey("ca"));
    assert(!trie.containsSubsequenceKey("at"));
    assert(!trie.containsSubsequenceKey("c"));
    assert(!trie.containsSubsequenceKey("cta"));
    assert(!trie.containsSubsequenceKey("cc"));
    assert(!trie.containsSubsequenceKey("ll"));
    assert(!trie.containsSubsequenceKey("lll"));
    assert(trie.containsSubsequenceKey("hellocat"));
    assert(trie.containsSubsequenceKey("ccaatt"));
    assert(trie.containsSubsequenceKey("zczaztz"));
    assert(trie.containsSubsequenceKey("hellop"));
}
