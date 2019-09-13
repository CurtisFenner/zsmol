const std = @import("std");
const assert = std.debug.assert;

const LinkAllocator = @import("linkalloc.zig");

const interpreter = @import("interpreter.zig");
const grammar = @import("grammar.zig");
const semantics = @import("semantics.zig");

fn blobFromFile(allocator: *std.mem.Allocator, file_name: []const u8) !grammar.Blob {
    const source_file = try std.fs.File.openRead(file_name);
    defer source_file.close();

    const block_size = 24;
    var size: usize = 0;
    var blocks = std.ArrayList([block_size]u8).init(allocator);
    defer blocks.deinit();
    while (true) {
        var block = [1]u8{0} ** block_size;
        const read = try source_file.read(block[0..block_size]);
        if (read == 0) {
            break;
        }
        size += read;
        try blocks.append(block);
    }

    var content = try allocator.alloc(u8, size);
    for (blocks.toSlice()) |block, i| {
        var to = std.math.min(size, block_size * (i + 1));
        var len = to - block_size * i;
        std.mem.copy(u8, content[block_size * i .. to], block[0..len]);
    }
    return grammar.Blob{
        .name = file_name,
        .content = content,
    };
}

const CommandArgs = struct {
    flags: [][2][]const u8,
    plain: []const []const u8,
    pub fn init(allocator: *std.mem.Allocator, list: []const []const u8) !CommandArgs {
        var flags = try allocator.alloc([2][]const u8, list.len);
        errdefer allocator.free(flags);
        var plain = try allocator.alloc([]const u8, list.len);
        var flag_index: usize = 0;
        var plain_index: usize = 0;
        var i: usize = 0;
        // TODO: Add "--" for all plain arguments to follow.
        while (i < list.len) {
            const v = list[i];
            if (v.len > 2 and v[0] == '-' and v[1] == '-') {
                // TODO: Reject duplicated flags.
                flags[flag_index][0] = v[2..];
                flags[flag_index][1] = list[i + 1];
                flag_index += 1;
                i += 1;
            } else {
                plain[plain_index] = v;
                plain_index += 1;
            }
            i += 1;
        }
        return CommandArgs{ .flags = flags[0..flag_index], .plain = plain[0..plain_index] };
    }

    pub fn find(self: CommandArgs, key: []const u8) ?[]const u8 {
        for (self.flags) |pair| {
            if (std.mem.eql(u8, key, pair[0])) {
                return pair[1];
            }
        }
        return null;
    }
};

pub fn mainInterpret(allocator: *std.mem.Allocator, command_args: []const []const u8) !u8 {
    var args = try CommandArgs.init(allocator, command_args);

    // TODO: Validate unknown flags.

    var sources = std.ArrayList(grammar.Source).init(allocator);
    defer sources.deinit();
    const stderr_file = try std.io.getStdErr();
    var parse_error: grammar.ParseErrorMessage = undefined;

    // Parse the source files.
    for (args.plain) |arg| {
        const blob = try blobFromFile(allocator, arg);
        const source = grammar.parseSource(allocator, blob, &parse_error) catch |err| switch (err) {
            error.OutOfMemory => return err,
            error.ParseError => {
                try parse_error.render(stderr_file, args.find("diagnostic-base"));
                return 40;
            },
        };
        try sources.append(source);
    }

    const program = try semantics.semantics(allocator, sources.toOwnedSlice());

    // TODO: Interpet.
    return 1;
}

pub fn printUsage() !void {
    const stderr = try std.io.getStdErr();
    try stderr.write("\n\tUSAGE:");
    try stderr.write("\tzsmol interpret [file1.smol] [file2.smol] [.....]\n");
}

pub fn main() !u8 {
    var arena = std.heap.ArenaAllocator.init(std.heap.direct_allocator);
    defer arena.deinit();
    const allocator = &arena.allocator;

    const args = try std.process.argsAlloc(allocator);
    const stderr_file = try std.io.getStdErr();
    if (args.len < 3) {
        try stderr_file.write("Expected at least three arguments\n");
        try printUsage();
        return @intCast(u8, 1);
    }

    if (std.mem.eql(u8, "interpet", args[1])) {
        return mainInterpret(allocator, args[2..]);
    }

    try stderr_file.write("Unknown compiler command.\n");
    try printUsage();
    return @intCast(u8, 1);
}
