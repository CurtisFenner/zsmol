// A very simple allocator, that's smarter than the
// FixedBufferAllocator.
const std = @import("std");
const Allocator = std.mem.Allocator;
const assert = std.debug.assert;

/// MaxHeap is an unresizable priority queue / max heap.
/// In addition to popMax() and push(), MaxHeap allows you to remove an object
/// at a given index.
/// Users of the MaxHeap are notified of updates to the heap so that they can
/// efficiently keep track of indexes for removal.
fn MaxHeap(comptime T: type) type {
    return struct {
        const Self = @This();
        items: []T,
        size: usize,

        fn init(items: []T) Self {
            return Self{
                .items = items,
                .size = 0,
            };
        }

        /// RETURNS true when this heap is empty, and no more elements can be
        /// removed.
        fn isEmpty(self: *const Self) bool {
            return self.size == 0;
        }

        /// RETURNS true when this heap is full, and no more elements can be
        /// added.
        fn isFull(self: *const Self) bool {
            return self.size == self.items.len;
        }

        /// RETURNS the current largest element in this heap.
        /// REQUIRES this heap is not emptpy.
        fn getMax(self: *Self) T {
            assert(self.size != 0);
            return self.items[0];
        }

        /// MODIFIES this heap to remove the largest element.
        /// RETURNS what was the largest element in this heap.
        /// REQUIRES this heap is not empty.
        fn popMax(self: *Self, notifier: var) T {
            assert(self.size != 0);
            const max = self.items[0];
            const last = self.items[self.size - 1];
            self.size -= 1;
            if (self.size != 0) {
                self.items[0] = last;
                self.bubbleDown(0, notifier);
            }
            return max;
        }

        /// MODIFIES this heap to contain the given value.
        /// REQUIRES this heap is not full.
        fn push(self: *Self, value: T, notifier: var) void {
            assert(self.size < self.items.len);
            self.items[self.size] = value;
            self.size += 1;
            self.bubbleUp(self.size - 1, notifier);
        }

        /// MODIFIES this heap to no longer contain the value at the given
        /// index.
        /// REQUIRES the given index is in-bounds.
        fn removeIndex(self: *Self, index: usize, notifier: var) T {
            assert(0 <= index and index < self.size);
            if (index == 0) {
                return self.popMax(notifier);
            }
            const value = self.items[index];
            assert(self.size != 1);
            var last = self.items[self.size - 1];
            self.items[index] = last;
            self.notify(index, notifier);
            self.size -= 1;

            // Only one of these will change anything.
            self.bubbleDown(index, notifier);
            self.bubbleUp(index, notifier);
            return value;
        }

        fn largerChild(self: *Self, index: usize, notifier: var) ?usize {
            var left_index = 2 * index + 1;
            var right_index = left_index + 1;

            var bigger: ?usize = null;
            if (left_index < self.size) {
                bigger = left_index;
            }
            if (right_index < self.size and notifier.smaller(self.items[left_index], self.items[right_index])) {
                bigger = right_index;
            }
            return bigger;
        }

        /// The indicated index hold a value 'smaller' than its children.
        fn bubbleDown(self: *Self, first_index: usize, notifier: var) void {
            var index = first_index;
            while (true) {
                var left_index = 2 * index + 1;
                var right_index = left_index + 1;
                if (left_index < self.size) {
                    // One or two children.
                    var bigger = self.items[left_index];
                    var bigger_index = left_index;
                    if (right_index < self.size and notifier.smaller(bigger, self.items[right_index])) {
                        bigger = self.items[right_index];
                        bigger_index = right_index;
                    }
                    if (notifier.smaller(self.items[index], bigger)) {
                        std.mem.swap(T, &self.items[index], &self.items[bigger_index]);
                        self.notify(index, notifier);
                        index = bigger_index;
                    } else {
                        self.notify(index, notifier);
                        return;
                    }
                } else {
                    // No children.
                    self.notify(index, notifier);
                    return;
                }
            }
        }

        /// The indicated index may hold a value 'bigger' than its parent.
        fn bubbleUp(self: *Self, first_index: usize, notifier: var) void {
            var index = first_index;
            while (0 < index) {
                var parent_index = (index - 1) / 2;
                if (notifier.smaller(self.items[parent_index], self.items[index])) {
                    std.mem.swap(T, &self.items[parent_index], &self.items[index]);
                    self.notify(index, notifier);
                    index = parent_index;
                } else {
                    self.notify(index, notifier);
                    return;
                }
            }
            self.notify(0, notifier);
        }

        fn notify(self: *Self, index: usize, notifier: var) void {
            notifier.notify(self.items[index], index);
        }
    };
}

const MaxHeapTest = struct {
    const Self = @This();
    const Heap = MaxHeap(usize);
    locations: [100]?usize = [1]?usize{null} ** 100,

    const Notifier = struct {
        fn notify(self: *Notifier, value: usize, index: usize) void {
            self.locations[value] = index;
        }
    };

    fn notify(self: *MaxHeapTest, value: usize, new_index: usize) void {
        self.locations[value] = new_index;
    }

    fn smaller(self: *MaxHeapTest, a: usize, b: usize) bool {
        return a < b;
    }

    fn check(self: MaxHeapTest, heap: *Heap) void {
        // Check notifications.
        var count: usize = 0;
        for (self.locations) |cloc, n| {
            if (cloc) |loc| {
                assert(loc < heap.size);
                if (n != heap.items[loc]) {
                    std.debug.warn("\n\nNOTIFICATION VIOLATION:\n");
                    std.debug.warn("\tNotified {} at index {}\n", n, loc);
                    std.debug.warn("\tHowever, items[{}] is {}\n", loc, heap.items[loc]);
                    assert(false);
                }
                count += 1;
            }
        }
        assert(count == heap.size);

        // Check heap invariant.
        for (heap.items[0..heap.size]) |item, i| {
            if (i == 0) continue;
            var parent = (i - 1) / 2;
            if (smaller(undefined, heap.items[parent], heap.items[i])) {
                std.debug.warn("\n\nHEAP INVARIANT VIOLATION:\n");
                std.debug.warn("\titems[{}] = {}\n", i, heap.items[i]);
                std.debug.warn("\titems[{}] = {}\n", parent, heap.items[parent]);
                assert(false);
            }
            assert(!smaller(undefined, heap.items[parent], heap.items[i]));
        }
    }

    fn push(self: *Self, heap: *Heap, value: usize) void {
        heap.push(value, self);
        self.check(heap);
        assert(!heap.isEmpty());
    }

    fn pop(self: *Self, heap: *Heap, expected: usize) void {
        const got = heap.popMax(self);
        if (expected != got) {
            std.debug.warn("\nExpected popMax() to return {} but got {}\n", expected, got);
            assert(false);
        }
        self.locations[got] = null;
        self.check(heap);
        assert(!heap.isFull());
    }

    fn remove(self: *Self, heap: *Heap, value: usize) void {
        var location = self.locations[value].?;
        assert(value == heap.removeIndex(location, self));
        self.locations[value] = null;
        self.check(heap);
        assert(!heap.isFull());
    }
};

test "MaxHeap" {
    var storage: [8]usize = undefined;
    var checker = MaxHeapTest{};
    var heap = MaxHeap(usize).init(storage[0..]);

    assert(heap.isEmpty());
    checker.push(&heap, 13);
    checker.push(&heap, 11);
    checker.push(&heap, 3);
    checker.push(&heap, 4);
    checker.push(&heap, 2);
    checker.pop(&heap, 13);
    checker.push(&heap, 8);
    checker.push(&heap, 12);
    checker.remove(&heap, 8);
    checker.push(&heap, 16);
    checker.push(&heap, 5);
    checker.push(&heap, 14);
    assert(heap.size == 8);
    assert(heap.isFull());
    checker.remove(&heap, 16);
    checker.pop(&heap, 14);
    checker.push(&heap, 7);
    checker.remove(&heap, 2);
    checker.pop(&heap, 12);
    checker.pop(&heap, 11);
    checker.remove(&heap, 4);
    checker.push(&heap, 9);
    checker.remove(&heap, 7);
    checker.push(&heap, 10);
    checker.pop(&heap, 10);
    checker.push(&heap, 15);
    checker.pop(&heap, 15);
    checker.pop(&heap, 9);
    checker.push(&heap, 1);
    checker.pop(&heap, 5);
    checker.remove(&heap, 3);
    checker.push(&heap, 6);
    checker.pop(&heap, 6);
}

pub const LinkAllocator = struct {
    const min_align: usize = 8; // TODO(#3154) @alignOf(usize);
    const min_words_for_open_block: usize = 8;

    /// The allocator interface.
    allocator: Allocator,

    /// The offsets into the heap of the open datablocks,
    /// organized as a complete binary heap.
    open_heap: MaxHeap(usize),

    /// The data_buffer, viewed as a sequence of usize.
    data_as_words: []usize,

    num_objects: usize,

    /// The maximum number of entries that this may contain. This is used to
    /// bound the size of the heap.
    max_objects: usize,

    const Block = struct {
        // points to [0]; stored at [end - 1]
        first_word: usize,
        // points to [end]; stored at [0]
        end_word: usize,
        // stored at [1]
        open_heap_location: ?usize,
        // data from [2, end - 1)
    };

    inline fn readBlock(self: *const LinkAllocator, block_at: usize) Block {
        const heap_info = self.data_as_words[block_at + 1];
        assert(heap_info <= self.max_objects);
        assert(block_at == self.data_as_words[self.data_as_words[block_at] - 1]);
        return Block{
            .first_word = block_at,
            .end_word = self.data_as_words[block_at],
            .open_heap_location = if (heap_info == self.max_objects) null else heap_info,
        };
    }

    inline fn sliceInitialWord(self: *LinkAllocator, slice: []const u8) usize {
        const difference = @ptrToInt(slice.ptr) - @ptrToInt(self.data_as_words.ptr);
        assert(difference % min_align == 0);
        return difference / min_align;
    }

    inline fn getBytes(self: *LinkAllocator, block: Block) []u8 {
        var data = @sliceToBytes(self.data_as_words);
        return data[@sizeOf(usize) * (block.first_word + 2) .. @sizeOf(usize) * (block.end_word - 1)];
    }

    inline fn updateOpenBlockLocation(self: *LinkAllocator, block_first_word: usize, new_location: ?usize) void {
        const index = block_first_word + 1;
        if (new_location) |location| {
            assert(location < self.max_objects);
            self.data_as_words[index] = location;
        } else {
            self.data_as_words[index] = self.max_objects;
        }
    }

    fn notify(self: *LinkAllocator, block_word: usize, heap_location: usize) void {
        self.updateOpenBlockLocation(block_word, heap_location);
    }

    /// smaller compares two free blocks by their size.
    fn smaller(self: *LinkAllocator, block_word_a: usize, block_word_b: usize) bool {
        const size_a = self.data_as_words[block_word_a] - block_word_a;
        const size_b = self.data_as_words[block_word_b] - block_word_b;
        return size_a < size_b;
    }

    pub fn init(unaligned_buffer: []u8) LinkAllocator {
        // Shrink both ends of the given buffer to the alignment of usize.
        const unaligned_base = @ptrToInt(unaligned_buffer.ptr);
        const aligned_from = std.mem.alignForward(unaligned_base, min_align) - unaligned_base;
        const aligned_to = std.mem.alignBackward(unaligned_base + unaligned_buffer.len, min_align) - unaligned_base;
        var buffer = unaligned_buffer[aligned_from..aligned_to];
        std.mem.set(u8, buffer, 127);

        var buffer_as_words = @alignCast(min_align, @bytesToSlice(usize, buffer));
        const max_objects = buffer_as_words.len / 5;

        var open_heap = MaxHeap(usize).init(buffer_as_words[0 .. max_objects + 1]);
        var data_as_words = buffer_as_words[max_objects + 1 ..];

        var self = LinkAllocator{
            .allocator = Allocator{ .reallocFn = realloc, .shrinkFn = shrink },
            .open_heap = open_heap,
            .num_objects = 0,
            .max_objects = max_objects,
            .data_as_words = data_as_words,
        };

        // Pointer to end of block
        self.data_as_words[0] = self.data_as_words.len;
        // Pointer to beginning of block
        self.data_as_words[self.data_as_words.len - 1] = 0;
        self.open_heap.push(0, &self);
        // Position in open heap
        assert(self.data_as_words[1] == 0);

        return self;
    }

    const Usable = struct {
        // The portion of the block usable for writing the location of the
        // block, then the data itself.
        // Index [@sizeOf(usize)] is aligned to the new_size.
        usable_bytes: []u8,
        open_block: Block,
    };

    fn getUsableAmount(self: *LinkAllocator, block_index: usize, new_size: usize, new_align: usize) ?Usable {
        const open_block = self.readBlock(block_index);
        var internal = self.getBytes(open_block);
        const internal_start = @ptrToInt(internal.ptr);
        assert(internal_start % min_align == 0);
        const data_start = std.mem.alignForward(internal_start + @sizeOf(usize), new_align);
        const metadata_size = data_start - internal_start;
        if (internal.len < new_size + metadata_size) {
            return null;
        }
        return Usable{
            .open_block = open_block,
            .usable_bytes = internal[metadata_size..],
        };
    }

    fn findUsableBlock(self: *LinkAllocator, new_size: usize, new_align: usize) !Usable {
        errdefer {
            std.debug.warn("!!! Could not allocate {} bytes with alignment {}\n", new_size, new_align);
            self.describe();
        }
        if (self.open_heap.isEmpty() or self.num_objects == self.max_objects) {
            return error.OutOfMemory;
        } else if (self.getUsableAmount(self.open_heap.getMax(), new_size, new_align) == null) {
            return error.OutOfMemory;
        }
        // Start from the largest block, and move to smaller children as
        // necessary.
        var index: usize = 0;
        var result: ?Usable = null;
        // TODO: We need to choose the bigger of the two children, so that the
        // entire tree is used.
        while (index < self.open_heap.size) {
            result = self.getUsableAmount(self.open_heap.items[index], new_size, new_align) orelse break;
            index = self.open_heap.largerChild(index, self) orelse break;
        }

        return result orelse error.OutOfMemory;
    }

    fn realloc(allocator: *Allocator, old_mem: []u8, old_align: u29, new_size: usize, req_new_align: u29) ![]u8 {
        var new_align = if (req_new_align < min_align) min_align else req_new_align;
        const self = @fieldParentPtr(LinkAllocator, "allocator", allocator);
        if (new_size == 0) {
            assert(old_mem.len != 0);
            self.free(old_mem);
            return old_mem[0..0];
        }

        assert(self.num_objects <= self.max_objects);

        // Find an open block with enough space for this allocation
        const usable = try self.findUsableBlock(new_size, new_align);
        _ = self.open_heap.removeIndex(usable.open_block.open_heap_location.?, self);

        // Fit the data into the open block
        const data_word_start = self.sliceInitialWord(usable.usable_bytes);
        var data = usable.usable_bytes[0..new_size];
        const post = usable.usable_bytes[std.mem.alignForward(new_size, min_align)..];
        const post_word_start = 1 + self.sliceInitialWord(post);
        const post_word_count = usable.open_block.end_word - post_word_start;
        if (min_words_for_open_block <= post_word_count) {
            // Split this block to make the remainder usable.
            self.data_as_words[usable.open_block.first_word] = post_word_start;
            self.data_as_words[post_word_start - 1] = usable.open_block.first_word;

            self.data_as_words[post_word_start] = usable.open_block.end_word;
            self.data_as_words[usable.open_block.end_word - 1] = post_word_start;
            self.open_heap.push(post_word_start, self);
        }

        // TODO: For allocations with large alignments, a lot of space could be
        // wasted before the data.
        self.data_as_words[data_word_start - 1] = usable.open_block.first_word;
        self.updateOpenBlockLocation(usable.open_block.first_word, null);

        self.num_objects += 1;
        if (old_mem.len != 0) {
            std.mem.copy(u8, data, old_mem);
            self.free(old_mem);
        }
        return data;
    }

    fn shrink(allocator: *Allocator, old_mem: []u8, req_old_align: u29, new_size: usize, req_new_align: u29) []u8 {
        var new_align = if (req_new_align < min_align) min_align else req_new_align;
        var old_align = if (req_old_align < min_align) min_align else req_old_align;

        const self = @fieldParentPtr(LinkAllocator, "allocator", allocator);
        assert(new_align <= old_align);
        if (new_size == 0) {
            self.free(old_mem);
        }
        // TODO: Recover open space from shrinking.
        return old_mem[0..new_size];
    }

    fn free(self: *LinkAllocator, old_mem: []u8) void {
        assert(old_mem.len != 0);
        const data_word = self.sliceInitialWord(old_mem);
        const direct_block_start = self.data_as_words[data_word - 1];
        const direct_block = self.readBlock(direct_block_start);
        assert(direct_block.open_heap_location == null);
        std.mem.set(u8, self.getBytes(direct_block), 7);

        var block_start = direct_block_start;
        var block_end = self.data_as_words[block_start];
        if (direct_block_start != 0) {
            var previous_block_start = self.data_as_words[direct_block_start - 1];
            const previous_block = self.readBlock(previous_block_start);
            if (previous_block.open_heap_location) |previous_block_open_heap_location| {
                // The previous block is open and should be merged with this block.
                _ = self.open_heap.removeIndex(previous_block_open_heap_location, self);
                block_start = previous_block.first_word;
                self.data_as_words[block_start] = block_end;
                self.data_as_words[block_end - 1] = block_start;
            }
        }

        if (block_end < self.data_as_words.len) {
            const next_block = self.readBlock(block_end);
            if (next_block.open_heap_location) |next_block_open_heap_location| {
                // The next block is open and should be merged with this block.
                _ = self.open_heap.removeIndex(next_block_open_heap_location, self);
                block_end = next_block.end_word;
                self.data_as_words[block_start] = block_end;
                self.data_as_words[block_end - 1] = block_start;
            }
        }

        self.num_objects -= 1;
        self.open_heap.push(block_start, self);
    }

    fn isEmpty(self: *const LinkAllocator) bool {
        return self.num_objects == 0;
    }

    fn describe(self: *const LinkAllocator) void {
        var bad = false;
        std.debug.warn("\n\n== LinkAllocator ==========================\n");
        std.debug.warn("\tobjects: {}/{}\n", self.num_objects, self.max_objects);
        std.debug.warn("\n");
        for (self.open_heap.items[0..self.open_heap.size]) |block_id, i| {
            const size = self.data_as_words[block_id] - block_id;
            std.debug.warn("\topen_heap[{}] = block {} (size {})\n", i, block_id, size);
        }
        std.debug.warn("\n");
        var index: usize = 0;
        while (index < self.data_as_words.len) {
            const block = self.readBlock(index);
            if (block.open_heap_location) |location| {
                std.debug.warn("\tOPEN block {}: ends at {} (size {})\n", block.first_word, block.end_word, block.end_word - block.first_word);
            } else {
                std.debug.warn("\tFILLED block {}: ends at {} (size {})\n", block.first_word, block.end_word, block.end_word - block.first_word);
            }
            std.debug.warn("\t\t[{}] is {}\n", block.end_word - 1, self.data_as_words[block.end_word - 1]);
            if (self.data_as_words[block.end_word - 1] != index) bad = true;
            index = block.end_word;
        }
        std.debug.warn("===========================================\n\n\n");
        if (bad) unreachable;
    }
};

test "simple" {
    var buffer = [_]u8{0} ** 240;
    std.debug.warn("\n");
    var la = LinkAllocator.init(buffer[0..]);
    var allocator = &la.allocator;

    la.describe();

    var obj1 = try allocator.alloc(usize, 2);
    obj1[0] = 111;
    obj1[1] = 222;

    la.describe();

    var obj2 = try allocator.alloc(usize, 3);
    obj2[0] = 333;
    obj2[1] = 444;
    obj2[2] = 555;

    la.describe();

    var obj3 = try allocator.alloc(usize, 1);
    obj3[0] = 666;

    la.describe();

    allocator.free(obj2);

    la.describe();

    allocator.free(obj3);

    la.describe();

    allocator.free(obj1);

    la.describe();
}
