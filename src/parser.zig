// parser.zig:
// A generic parsing library for building recursive descent grammars out of
// parsing combinators.

const std = @import("std");
const assert = std.debug.assert;
const ArrayList = std.ArrayList;
const TypeInfo = @import("builtin").TypeInfo;
const TypeId = @import("builtin").TypeId;

////////////////////////////////////////////////////////////////////////////////

/// A Blob represents an in-memory representation of a source file. It contains
/// the whole contents of the file to make generating excerpts easy.
pub const Blob = struct {
    name: []const u8,
    content: []const u8,
};

/// A Location represents a range of characters in a text Blob.
pub const Location = struct {
    blob: *const Blob,
    begin: usize,
    end: usize,

    pub fn span(begin: Location, end: Location) Location {
        assert(begin.blob == end.blob);
        return Location{
            .blob = begin.blob,
            .begin = begin.begin,
            .end = end.end,
        };
    }

    const LINE_NUM_WIDTH: usize = 10;
    const LINE_CONTEXT: usize = 1;
    const TAB_SIZE: usize = 4;

    /// Prints this location as a phase in the format
    /// `"filename:startline:startcol-endline:endcol"` to the given file.
    /// For example, `"dir/file.txt:10:15-10:20"`.
    pub fn printPosition(location: Location, file: var, diagnostic_base: ?[]const u8) !void {
        var start_line: usize = 0;
        var start_column: usize = 0;
        var end_line: usize = 1;
        var end_column: usize = 1;
        for (location.blob.content) |c, i| {
            if (i == location.begin) {
                start_line = end_line;
                start_column = end_column;
            }
            if (i == location.end) {
                break;
            }

            if (c == '\n') {
                end_line += 1;
                end_column = 1;
            } else if (c == '\r') {
                // Ignore
            } else if (c == '\t') {
                end_column += TAB_SIZE - (end_column + TAB_SIZE - 1) % TAB_SIZE;
            } else {
                end_column += 1;
            }
        }

        if (diagnostic_base != null and std.mem.startsWith(u8, location.blob.name, diagnostic_base.?)) {
            try file.writeAll(location.blob.name[diagnostic_base.?.len..]);
        } else {
            try file.writeAll(location.blob.name);
        }
        try file.writeAll(":");
        var buffer = [_]u8{0} ** 32;
        const format = std.fmt.FormatOptions{};
        var width = std.fmt.formatIntBuf(&buffer, start_line, 10, false, format);
        try file.writeAll(buffer[0..width]);
        try file.writeAll(":");
        width = std.fmt.formatIntBuf(&buffer, start_column, 10, false, format);
        try file.writeAll(buffer[0..width]);
        try file.writeAll("-");
        width = std.fmt.formatIntBuf(&buffer, end_line, 10, false, format);
        try file.writeAll(buffer[0..width]);
        try file.writeAll(":");
        width = std.fmt.formatIntBuf(&buffer, end_column, 10, false, format);
        try file.writeAll(buffer[0..width]);
    }

    pub fn printExcerpt(location: Location, file: var) !void {
        var line: usize = 0;
        var line_begin: usize = undefined;
        var line_end: usize = undefined;
        for (location.blob.content) |c, i| {
            if (i == location.begin) {
                line_begin = line;
            }
            if (i == location.end) {
                line_end = line;
            }
            if (c == '\n') {
                line += 1;
            }
        }

        line = 0;
        var column: usize = 0;
        var beginning_of_line = true;
        var caret_low: ?usize = null;
        var caret_high: usize = 0;
        for (location.blob.content) |c, i| {
            const should_draw_line = line_begin <= line + LINE_CONTEXT and line <= line_end + LINE_CONTEXT;
            if (should_draw_line and beginning_of_line) {
                var buffer = [_]u8{0} ** 32;
                const width = std.fmt.formatIntBuf(&buffer, line + 1, 10, false, std.fmt.FormatOptions{});
                var padding = LINE_NUM_WIDTH - width;
                while (padding != 0) {
                    try file.writeAll(" ");
                    padding -= 1;
                }
                try file.writeAll(buffer[0..width]);
                try file.writeAll(" | ");
                beginning_of_line = false;
            }

            if (c == '\n') {
                column = 0;
                line += 1;
                beginning_of_line = true;
                if (should_draw_line) {
                    try file.writeAll("\n");
                }
            } else if (c == '\t') {
                const previous_column = column;
                column += TAB_SIZE - column % TAB_SIZE;
                var actual_tab_width = column - previous_column;
                if (should_draw_line) {
                    while (actual_tab_width != 0) {
                        try file.writeAll(" ");
                        actual_tab_width -= 1;
                    }
                }
            } else if (c == '\r') {
                // Do nothing
            } else {
                if (should_draw_line) {
                    var rep: u8 = undefined;
                    if (32 <= c and c <= 127) {
                        rep = c;
                    } else {
                        rep = '?';
                    }
                    try file.writeAll(&[_]u8{rep});
                    if (rep != ' ' and location.begin <= i and i < location.end) {
                        if (caret_low == null) {
                            caret_low = column;
                        }
                        caret_high = column;
                    }
                }
                column += 1;
            }

            if (c != '\n' and i == location.blob.content.len - 1 and should_draw_line) {
                // Insert an artificial line break if the file doesn't end with
                // one.
                try file.writeAll("\n");
                beginning_of_line = true;
            }

            if (should_draw_line and beginning_of_line) {
                // Draw carets
                if (caret_low) |low| {
                    try file.writeAll(" " ** LINE_NUM_WIDTH);
                    try file.writeAll(" | ");
                    var pad = low;
                    while (pad != 0) {
                        try file.writeAll(" ");
                        pad -= 1;
                    }
                    var width = caret_high + 1 - low;
                    while (width != 0) {
                        try file.writeAll("^");
                        width -= 1;
                    }
                    try file.writeAll("\n");
                }
                caret_low = null;
                caret_high = undefined;
            }
        }
    }
};

/// A ErrorMessage represents an error message produced when parsing.
pub const ErrorMessage = struct {
    pub const Entry = union(enum) {
        Text: []const u8,
        AtLocation: Location,
    };

    entry_count: usize,
    entries_storage: [64]Entry = undefined,

    pub fn render(e: ErrorMessage, file: var, diagnostic_base: ?[]const u8) !void {
        try file.writeAll("ERROR:\n");
        for (e.entries_storage[0..e.entry_count]) |entry, i| {
            switch (entry) {
                .Text => |t| try file.writeAll(t),
                .AtLocation => |loc| {
                    try file.writeAll(" at ");
                    try loc.printPosition(file, diagnostic_base);
                    try file.writeAll(":\n");
                    try loc.printExcerpt(file);
                    if (i + 1 != e.entry_count) try file.writeAll("\n");
                },
            }
        }
    }

    pub fn make(entries: []const ErrorMessage.Entry) ErrorMessage {
        var self = ErrorMessage{ .entry_count = entries.len };
        assert(entries.len < self.entries_storage.len);
        std.mem.copy(ErrorMessage.Entry, &self.entries_storage, entries);
        return self;
    }
};

pub fn Combinators(comptime Token: type) type {
    return struct {
        /// A Stream represents a tokenized text source.
        pub const Stream = struct {
            allocator: *std.mem.Allocator,

            /// The tokens in the stream.
            tokens: []const Token,

            /// The locations of the tokens.
            /// locations.len == tokens.len + 1. The final Location is the
            /// "end of file".
            locations: []const Location,

            fn deinit(self: Stream) void {
                self.allocator.free(self.locations);
                for (self.tokens) |token| {
                    token.deinit(self.allocator);
                }
                self.allocator.free(self.tokens);
            }
        };

        /// Represents a field in a sequence AST or a variant in a sum AST.
        pub const Field = struct {
            /// The name of the field.
            name: []const u8,

            /// The type of the field.
            CT: type,

            /// The minimum number of elements to take (e.g., `0` for `*` and
            /// `1` for `+`).
            min_take_count: usize,

            /// The maximum number of elements to take (e.g., `1` for `?`)
            /// A max_take_count of zero means no limit.
            max_take_count: usize,

            /// The type for separating the field when it is repeated.
            /// Separators are dropped from the AST after parsing.
            separator: ?type,

            /// The error message to write when this field fails to parse.
            /// Only possible for fields with a min_take_count of at least 1.
            /// The error message will be formatted as
            /// "<cut_message> at file:location"
            /// An example cut_message is
            /// `"Expected a `)` to finish a function call"`.
            cut_message: ?[]const u8,

            fn structType(comptime self: Field) type {
                if (self.max_take_count == 1) {
                    if (self.min_take_count == 1) {
                        return self.CT;
                    }
                    return ?*const self.CT;
                }
                return []const self.CT;
            }
        };

        const grammar = @This();

        /// Fluent provides a "fluent interface" for building AST types out of
        /// combinators.
        /// For example, to define an AST for `'(' word+ ')'`,
        /// ```
        /// comb.fluent.req("open", TOpen).plusSep(TSpace, "word", Word).req("close", TClose).seq();
        /// ```
        pub const Fluent = struct {
            fields: []const Field,

            /// Parse a required field. If this field isn't found, the
            /// containing sequence will fail to parse.
            fn req(comptime self: Fluent, comptime name: []const u8, comptime CT: type) Fluent {
                return Fluent{
                    .fields = self.fields ++ [_]Field{Field{
                        .name = name,
                        .CT = CT,
                        .min_take_count = 1,
                        .max_take_count = 1,
                        .separator = null,
                        .cut_message = null,
                    }},
                };
            }

            /// If the previous element fails to parse, the overall sequence
            /// should fail with the given error message.
            fn cut(comptime self: Fluent, comptime expected: []const u8) Fluent {
                assert(self.fields.len != 0);

                // TODO: Working around ziglang bug #5293
                // const init = self.fields[0 .. self.fields.len - 1];
                var init: []const Field = &[_]Field{};
                var i = 0;
                while (i + 1 < self.fields.len) {
                    init = init ++ &[_]Field{self.fields[i]};
                    i += 1;
                }

                const last = self.fields[self.fields.len - 1];
                assert(last.min_take_count != 0);
                return Fluent{
                    .fields = init ++ [_]Field{Field{
                        .name = last.name,
                        .CT = last.CT,
                        .min_take_count = last.min_take_count,
                        .max_take_count = last.max_take_count,
                        .separator = last.separator,
                        .cut_message = expected,
                    }},
                };
            }

            /// Parse an optional field. If this field isn't found, parsing will
            /// continue on the next field in the sequence/choice.
            fn opt(comptime self: Fluent, comptime name: []const u8, comptime CT: type) Fluent {
                return Fluent{
                    .fields = self.fields ++ [_]Field{Field{
                        .name = name,
                        .CT = CT,
                        .min_take_count = 0,
                        .max_take_count = 1,
                        .separator = null,
                        .cut_message = null,
                    }},
                };
            }

            /// Parse 0 or more entries of the same type.
            fn star(comptime self: Fluent, comptime name: []const u8, comptime CT: type) Fluent {
                return Fluent{
                    .fields = self.fields ++ [_]Field{Field{
                        .name = name,
                        .CT = CT,
                        .min_take_count = 0,
                        .max_take_count = 0,
                        .separator = null,
                        .cut_message = null,
                    }},
                };
            }

            /// Parse 1 or more entries of the same type.
            fn plus(comptime self: Fluent, comptime name: []const u8, comptime CT: type) Fluent {
                return Fluent{
                    .fields = self.fields ++ [_]Field{Field{
                        .name = name,
                        .CT = CT,
                        .min_take_count = 1,
                        .max_take_count = 0,
                        .separator = null,
                        .cut_message = null,
                    }},
                };
            }

            /// Parse 0 or more entries of the same type, each separated by the
            /// given separator AST. The separators are dropped from the
            /// resulting value.
            fn starSep(comptime self: Fluent, comptime name: []const u8, comptime CT: type, comptime comma: type) Fluent {
                return Fluent{
                    .fields = self.fields ++ [_]Field{Field{
                        .name = name,
                        .CT = CT,
                        .min_take_count = 0,
                        .max_take_count = 0,
                        .separator = comma,
                        .cut_message = null,
                    }},
                };
            }

            /// Plus 1 or more entries of the same type, each separated by the
            /// given separator AST. The separators are dropped from the
            /// resulting value.
            fn plusSep(comptime self: Fluent, comptime name: []const u8, comptime CT: type, comptime comma: type) Fluent {
                return Fluent{
                    .fields = self.fields ++ [_]Field{Field{
                        .name = name,
                        .CT = CT,
                        .min_take_count = 1,
                        .max_take_count = 0,
                        .separator = comma,
                        .cut_message = null,
                    }},
                };
            }

            fn customField(comptime self: Fluent, comptime field: Field) Fluent {
                return Fluent{
                    .fields = self.fields ++ []Field{field},
                };
            }

            fn seq(comptime self: Fluent, comptime Target: type) type {
                return grammar.SequenceParser(Target, self.fields);
            }
        };

        fn InternalParseUnion(comptime T: type) type {
            return union(enum) {
                Result: InternalParseResult(T),
                NoMatch: void,
                Error: ErrorMessage,
            };
        }

        const FieldResultUnion = union(enum) {
            Success: void,
            Fail: void,
            Error: ErrorMessage,
        };

        fn InternalParseResult(comptime T: type) type {
            return struct {
                value: T,
                consumed: usize,
            };
        }

        /// A parser that matches only the end of a Stream.
        pub const EofParser = struct {
            nothing: usize,
            pub const Parser = struct {
                pub fn _deinit(allocator: *std.mem.Allocator, self: EofParser) void {}

                pub fn _parse(allocator: *std.mem.Allocator, stream: Stream, from: usize) error{OutOfMemory}!InternalParseUnion(EofParser) {
                    if (stream.tokens.len != from) {
                        return InternalParseUnion(EofParser){ .NoMatch = {} };
                    }
                    return InternalParseUnion(EofParser){
                        .Result = InternalParseResult(EofParser){ .consumed = 0, .value = EofParser{ .nothing = undefined } },
                    };
                }
            };
        };

        /// A parser that matches a single token of the given type.
        pub fn TokenParser(comptime Into: type, comptime pattern: @TagType(Token)) type {
            return struct {
                pub fn deinit(allocator: *std.mem.Allocator, self: Into) void {}

                pub fn _parse(allocator: *std.mem.Allocator, stream: Stream, from: usize) error{OutOfMemory}!InternalParseUnion(Into) {
                    if (stream.tokens.len == from) {
                        return InternalParseUnion(Into){ .NoMatch = {} };
                    }
                    const head = stream.tokens[from];
                    switch (head) {
                        pattern => |value| return InternalParseUnion(Into){
                            .Result = InternalParseResult(Into){
                                .consumed = 1,
                                .value = Into{
                                    .value = value,
                                    .location = stream.locations[from],
                                },
                            },
                        },
                        else => return InternalParseUnion(Into){ .NoMatch = {} },
                    }
                }
            };
        }

        pub fn ChoiceParser(comptime Into: type) type {
            return struct {
                pub fn _parse(allocator: *std.mem.Allocator, stream: Stream, from: usize) error{OutOfMemory}!InternalParseUnion(Into) {
                    const fields = std.meta.fields(Into);
                    inline for (fields) |field| {
                        if (comptime std.meta.activeTag(@typeInfo(field.field_type)) != TypeId.Pointer or !@typeInfo(field.field_type).Pointer.is_const) {
                            @compileError("ChoiceParser requires field `" ++ field.name ++ "` in `" ++ @typeName(Into) ++ "` to be a const pointer");
                        }
                        const FieldType = @typeInfo(field.field_type).Pointer.child;
                        // TODO(#2727): Shouldn't really need inline.
                        const never_inline_modifier: std.builtin.CallOptions = std.builtin.CallOptions{ .modifier = .never_inline };
                        const result = try @call(never_inline_modifier, FieldType.Parser._parse, .{ allocator, stream, from });
                        // TODO(#2727): Use a switch.
                        const Tags = @TagType(@TypeOf(result));
                        const tag = @as(Tags, result);
                        if (tag == Tags.Result) {
                            var ptr = try allocator.create(@TypeOf(result.Result.value));
                            ptr.* = result.Result.value;
                            return InternalParseUnion(Into){
                                .Result = InternalParseResult(Into){
                                    .value = @unionInit(Into, field.name, ptr),
                                    .consumed = result.Result.consumed,
                                },
                            };
                        } else if (tag == Tags.NoMatch) {
                            // Continue to the next variant.
                        } else if (tag == Tags.Error) {
                            return InternalParseUnion(Into){ .Error = result.Error };
                        } else {
                            assert(false);
                        }
                    }
                    return InternalParseUnion(Into){ .NoMatch = {} };
                }
            };
        }

        pub fn SequenceParser(comptime Into: type, comptime fields: []const Field) type {
            if (fields.len == 0) {
                @compileError("SequenceParser requires at least one field");
            }

            return struct {
                pub fn parse(allocator: *std.mem.Allocator, stream: Stream, parse_error: *ErrorMessage) error{
                    OutOfMemory,
                    ParseError,
                }!Into {
                    const ru = try @This()._parse(allocator, stream, 0);
                    switch (ru) {
                        .NoMatch => {
                            parse_error.* = ErrorMessage{ .entry_count = 2 };
                            parse_error.*.entries_storage[0] = ErrorMessage.Entry{ .Text = "Expected " ++ @typeName(Into) };
                            parse_error.*.entries_storage[1] = ErrorMessage.Entry{ .AtLocation = stream.locations[0] };
                            return error.ParseError;
                        },
                        .Error => |e| {
                            parse_error.* = e;
                            return error.ParseError;
                        },
                        .Result => |result| {
                            if (result.consumed != stream.tokens.len) {
                                parse_error.* = ErrorMessage.make(&[_]ErrorMessage.Entry{
                                    ErrorMessage.Entry{ .Text = "Unexpected end to " ++ @typeName(Into) },
                                    ErrorMessage.Entry{ .AtLocation = stream.locations[result.consumed] },
                                });
                                return error.ParseError;
                            }
                            return result.value;
                        },
                    }
                }

                fn _parseField(comptime field: Field, result: var, stream: Stream, from: usize, consumed: *usize, allocator: *std.mem.Allocator) error{OutOfMemory}!FieldResultUnion {
                    // Parse a repeated field.
                    // TODO: Recover list's memory.
                    var list = std.ArrayList(field.CT).init(allocator);

                    while (field.max_take_count <= 0 or list.items.len < field.max_take_count) {
                        // Parse a separator, if any.
                        var sep_consumed: usize = 0;
                        if (comptime field.separator) |sep| {
                            if (list.items.len != 0) {
                                const separator = try sep.Parser._parse(allocator, stream, from + consumed.*);
                                // TODO: free separator's memory
                                switch (separator) {
                                    .Result => |r| {
                                        consumed.* += r.consumed;
                                        sep_consumed = r.consumed;
                                    },
                                    .NoMatch => {
                                        break;
                                    },
                                    .Error => |e| {
                                        return FieldResultUnion{ .Error = e };
                                    },
                                }
                            }
                        }

                        // Parse an element in the list.
                        var element: field.CT = undefined;
                        const raw = try field.CT.Parser._parse(allocator, stream, from + consumed.*);
                        switch (raw) {
                            .Result => |r| {
                                element = r.value;
                                consumed.* += r.consumed;
                            },
                            .Error => |e| {
                                return FieldResultUnion{ .Error = e };
                            },
                            .NoMatch => {
                                break;
                            },
                        }
                        try list.append(element);
                    }

                    var enough = list.items.len >= field.min_take_count;
                    if (!enough) {
                        if (field.cut_message) |cut_message| {
                            return FieldResultUnion{
                                .Error = ErrorMessage.make(&[_]ErrorMessage.Entry{
                                    ErrorMessage.Entry{ .Text = cut_message },
                                    ErrorMessage.Entry{ .AtLocation = stream.locations[from + consumed.*] },
                                }),
                            };
                        }
                        return FieldResultUnion{ .Fail = {} };
                    }

                    // Attach the sub-result onto the AST.
                    if (comptime std.mem.eql(u8, "_", field.name)) {
                        assert(field.max_take_count == 1);
                        // TODO: Free the memory of the elements in the list
                    } else {
                        if (field.max_take_count == 1) {
                            if (field.min_take_count == 0) {
                                if (list.items.len == 1) {
                                    // TODO: Recover memory?
                                    @field(result, field.name) = &list.items[0];
                                } else {
                                    // TODO: Recover memory?
                                    @field(result, field.name) = null;
                                }
                            } else {
                                // TODO: Recover memory
                                @field(result, field.name) = list.items[0];
                            }
                        } else {
                            @field(result, field.name) = list.items;
                        }
                    }
                    return FieldResultUnion{ .Success = {} };
                }

                pub fn _parse(allocator: *std.mem.Allocator, stream: Stream, from: usize) error{OutOfMemory}!InternalParseUnion(Into) {
                    var result: Into = undefined;
                    var consumed: usize = 0;
                    // TODO: Use a bump-allocator that doesn't require recursive deallocation.

                    // TODO(ziglang #5170):
                    inline for (fields) |field| {
                        comptime const never_inline_modifier = std.builtin.CallOptions{ .modifier = .never_inline };
                        const r = try @call(never_inline_modifier, @This()._parseField, .{ field, &result, stream, from, &consumed, allocator });
                        const Tags = @TagType(@TypeOf(r));
                        const tag = @as(Tags, r);
                        // TODO(#2727)
                        if (tag == Tags.Success) {
                            // Continue to the next field.
                        } else if (tag == Tags.Fail) {
                            return InternalParseUnion(Into){ .NoMatch = {} };
                        } else if (tag == Tags.Error) {
                            return InternalParseUnion(Into){ .Error = r.Error };
                        } else {
                            assert(false);
                        }
                    }

                    // Produce the finished result, including Location annotations.
                    result.location = stream.locations[from].span(stream.locations[from + consumed - 1]);
                    return InternalParseUnion(Into){
                        .Result = InternalParseResult(Into){
                            .consumed = consumed,
                            .value = result,
                        },
                    };
                }
            };
        }

        /// The `fluent` instance is the start for the Fluent interface.
        pub const fluent = Fluent{ .fields = &[_]Field{} };
    };
}

test "Separator" {
    const Token = union(enum) {
        A: void,
        B: void,
    };
    const comb = Combinators(Token);

    const A = struct {
        value: void,
        const Parser = comb.TokenParser(@This(), Token.A);
        location: Location,
    };
    const B = struct {
        value: void,
        const Parser = comb.TokenParser(@This(), Token.B);
        location: Location,
    };

    const C = struct {
        list: []const A,
        const Parser = comb.fluent.plusSep("list", A, B).seq(@This());
        location: Location,
    };

    const stream = comb.Stream{
        .allocator = undefined,
        .tokens = &[_]Token{Token{ .A = {} }},
        .locations = &[_]Location{ undefined, undefined },
    };

    var buffer: [4000]u8 = undefined;
    var buffer_allocator = std.heap.FixedBufferAllocator.init(&buffer);
    var allocator = &buffer_allocator.allocator;
    const result = try C.Parser.parse(allocator, stream, undefined);
}

test "Lisp" {
    const Token = union(enum) {
        TOpen: void,
        TClose: void,
        TAtom: []const u8,
    };

    const comb = Combinators(Token);

    const Lexer = struct {
        fn tokenize(allocator: *std.mem.Allocator, blob: *const Blob) !comb.Stream {
            var tokens = std.ArrayList(Token).init(allocator);
            var locations = std.ArrayList(Location).init(allocator);
            for (blob.content) |c, i| {
                if (c == ' ') {
                    continue;
                }
                try locations.append(Location{ .blob = blob, .begin = i, .end = i + 1 });
                if (c == '(') {
                    try tokens.append(Token{ .TOpen = {} });
                } else if (c == ')') {
                    try tokens.append(Token{ .TClose = {} });
                } else {
                    try tokens.append(Token{ .TAtom = blob.content[i .. i + 1] });
                }
            }
            try locations.append(Location{ .blob = blob, .begin = blob.content.len, .end = blob.content.len });
            return comb.Stream{
                .allocator = allocator,
                .tokens = tokens.toOwnedSlice(),
                .locations = locations.toOwnedSlice(),
            };
        }
    };

    const AST = struct {
        const Open = struct {
            value: void,
            const Parser = comb.TokenParser(@This(), Token.TOpen);
            location: Location,
        };
        const Close = struct {
            value: void,
            const Parser = comb.TokenParser(@This(), Token.TClose);
            location: Location,
        };
        const Atom = struct {
            value: []const u8,
            const Parser = comb.TokenParser(@This(), Token.TAtom);
            location: Location,
        };
        const Expr = union(enum) {
            Atom: *const Atom,
            Phrase: *const Phrase,
            const Parser = comb.ChoiceParser(@This());
        };
        const Phrase = struct {
            open: Open,
            args: []const Expr,
            close: Close,
            const Parser = comb.fluent //
                .req("open", Open) //
                .star("args", Expr) //
                .req("close", Close).cut("need `)`") //
                .seq(@This());
            location: Location,
        };
    };

    var buffer: [4000]u8 = undefined;
    var buffer_allocator = std.heap.FixedBufferAllocator.init(&buffer);
    var allocator = &buffer_allocator.allocator;
    const blob = Blob{ .name = "test", .content = "(a (b c d) (e f) () g)" };
    const stream = try Lexer.tokenize(allocator, &blob);

    var parse_error: ErrorMessage = undefined;

    const stdout_file = std.io.getStdOut();
    const result = AST.Phrase.Parser.parse(allocator, stream, &parse_error) catch |err| switch (err) {
        error.ParseError => |e| {
            try parse_error.render(stdout_file, "");
            return e;
        },
        error.OutOfMemory => |e| return e,
    };
    assert(result.args.len == 5);
    assert(std.mem.eql(u8, result.args[0].Atom.value, "a"));
    assert(result.args[1].Phrase.args.len == 3);
    assert(result.args[2].Phrase.args.len == 2);
    assert(result.args[3].Phrase.args.len == 0);
    assert(std.mem.eql(u8, result.args[4].Atom.value, "g"));
}
