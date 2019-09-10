// parser.zig:
// A generic parsing library for building recursive descent grammars out of
// parsing combinators.

const std = @import("std");
const assert = std.debug.assert;
const ArrayList = std.ArrayList;
const TypeInfo = @import("builtin").TypeInfo;
const TypeId = @import("builtin").TypeId;

////////////////////////////////////////////////////////////////////////////////

/// A Blob represents an in-memory representation of a source.
/// This is used for generating error messages that include context.
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

    pub fn printPosition(location: Location, file: var) !void {
        var start_line: usize = undefined;
        var start_column: usize = undefined;
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
                end_column += TAB_SIZE - end_column % TAB_SIZE;
            } else {
                end_column += 1;
            }
        }

        try file.write(location.blob.name);
        try file.write(":");
        var buffer = [_]u8{0} ** 32;
        var width: usize = undefined;
        const format = std.fmt.FormatOptions{};
        width = std.fmt.formatIntBuf(&buffer, start_line, 10, false, format);
        try file.write(buffer[0..width]);
        try file.write(":");
        width = std.fmt.formatIntBuf(&buffer, start_column, 10, false, format);
        try file.write(buffer[0..width]);
        try file.write("-");
        width = std.fmt.formatIntBuf(&buffer, end_line, 10, false, format);
        try file.write(buffer[0..width]);
        try file.write(":");
        width = std.fmt.formatIntBuf(&buffer, end_column, 10, false, format);
        try file.write(buffer[0..width]);
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
                    try file.write(" ");
                    padding -= 1;
                }
                try file.write(buffer[0..width]);
                try file.write(" | ");
                beginning_of_line = false;
            }

            if (c == '\n') {
                column = 0;
                line += 1;
                beginning_of_line = true;
                if (should_draw_line) {
                    try file.write("\n");
                }
            } else if (c == '\t') {
                const previous_column = column;
                column += TAB_SIZE - column % TAB_SIZE;
                var actual_tab_width = column - previous_column;
                if (should_draw_line) {
                    while (actual_tab_width != 0) {
                        try file.write(" ");
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
                    try file.write([_]u8{rep});
                    if (rep != ' ' and location.begin <= i and i < location.end) {
                        if (caret_low == null) {
                            caret_low = column;
                        }
                        caret_high = column;
                    }
                }
                column += 1;
            }

            if (i == location.blob.content.len - 1 and should_draw_line) {
                // Insert an artificial line break if the file doesn't end with
                // one.
                try file.write("\n");
                beginning_of_line = true;
            }

            if (should_draw_line and beginning_of_line) {
                // Draw carets
                if (caret_low) |low| {
                    try file.write(" " ** LINE_NUM_WIDTH);
                    try file.write(" | ");
                    var pad = low;
                    while (pad != 0) {
                        try file.write(" ");
                        pad -= 1;
                    }
                    var width = caret_high + 1 - low;
                    while (width != 0) {
                        try file.write("^");
                        width -= 1;
                    }
                    try file.write("\n");
                }
                caret_low = null;
                caret_high = undefined;
            }
        }
    }
};

/// A ParseErrorMessage represents an error message produced when parsing.
pub const ParseErrorMessage = struct {
    pub const Entry = union(enum) {
        Text: []const u8,
        AtLocation: Location,
    };

    entries: []const Entry,

    pub fn render(e: ParseErrorMessage, file: var) !void {
        try file.write("ERROR: ");
        for (e.entries) |entry| {
            switch (entry) {
                .Text => |t| try file.write(t),
                .AtLocation => |loc| {
                    try file.write(" at ");
                    try loc.printPosition(file);
                    try file.write(":\n");
                    try loc.printExcerpt(file);
                },
            }
        }
    }
};

const ParseErrors = error{
    ParseError,
    OutOfMemory,
};

/// Internal parse errors.
const InternalParseErrors = error{
    NoMatch,
    ParseError,
    OutOfMemory,
};

pub fn makeParseError(allocator: *std.mem.Allocator, location: Location, cut_message: []const u8) !ParseErrorMessage {
    var entries = try allocator.alloc(ParseErrorMessage.Entry, 2);
    entries[0] = ParseErrorMessage.Entry{ .Text = cut_message };
    entries[1] = ParseErrorMessage.Entry{ .AtLocation = location };
    return ParseErrorMessage{ .entries = entries };
}

pub fn Combinators(comptime Token: type) type {
    return struct {
        /// A Stream represents a tokenized text source.
        pub const Stream = struct {
            /// The tokens in the stream.
            tokens: []const Token,

            /// The locations of the tokens.
            /// locations.len == tokens.len + 1. The final Location is the
            /// "end of file".
            locations: []const Location,
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
                const init = self.fields[0 .. self.fields.len - 1];
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
                Error: ParseErrorMessage,
            };
        }

        const FieldResultUnion = union(enum) {
            Success: void,
            Fail: void,
            Error: ParseErrorMessage,
        };

        fn InternalParseResult(comptime T: type) type {
            return struct {
                value: T,
                consumed: usize,
            };
        }

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
                        const result = try @noInlineCall(FieldType.Parser._parse, allocator, stream, from);
                        // TODO(#27272): Use a switch.
                        const Tags = @TagType(@typeOf(result));
                        const tag = Tags(result);
                        if (tag == Tags.Result) {
                            var ptr = try allocator.create(@typeOf(result.Result.value));
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
                pub fn parse(allocator: *std.mem.Allocator, stream: Stream, parse_error: *ParseErrorMessage) error{
                    OutOfMemory,
                    ParseError,
                }!Into {
                    const ru = try @This()._parse(allocator, stream, 0);
                    switch (ru) {
                        .NoMatch => {
                            var entries = try allocator.alloc(ParseErrorMessage.Entry, 2);
                            entries[0] = ParseErrorMessage.Entry{ .Text = "Expected " ++ @typeName(Into) };
                            entries[1] = ParseErrorMessage.Entry{ .AtLocation = stream.locations[0] };
                            parse_error.* = ParseErrorMessage{ .entries = entries };
                            return error.ParseError;
                        },
                        .Error => |e| {
                            parse_error.* = e;
                            return error.ParseError;
                        },
                        .Result => |result| {
                            if (result.consumed != stream.tokens.len) {
                                var entries = try allocator.alloc(ParseErrorMessage.Entry, 2);
                                entries[0] = ParseErrorMessage.Entry{ .Text = "Unexpected end to " ++ @typeName(Into) };
                                entries[1] = ParseErrorMessage.Entry{ .AtLocation = stream.locations[result.consumed] };
                                parse_error.* = ParseErrorMessage{ .entries = entries };
                                return error.ParseError;
                            }
                            return result.value;
                        },
                    }
                }

                fn _parseField(comptime field: Field, result: var, stream: Stream, from: usize, consumed: *usize, allocator: *std.mem.Allocator) error{OutOfMemory}!FieldResultUnion {
                    // Parse a repeated field.
                    var list = std.ArrayList(field.CT).init(allocator);

                    while (field.max_take_count <= 0 or list.count() < field.max_take_count) {
                        // Parse a separator, if any.
                        var sep_consumed: usize = 0;
                        if (comptime field.separator) |sep| {
                            if (list.count() != 0) {
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

                    var enough = list.count() >= field.min_take_count;
                    if (!enough) {
                        if (field.cut_message) |cut_message| {
                            var entries = try allocator.alloc(ParseErrorMessage.Entry, 2);
                            entries[0] = ParseErrorMessage.Entry{ .Text = cut_message };
                            entries[1] = ParseErrorMessage.Entry{ .AtLocation = stream.locations[from + consumed.*] };
                            return FieldResultUnion{ .Error = ParseErrorMessage{ .entries = entries } };
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
                                if (list.count() == 1) {
                                    // TODO: Recover memory?
                                    @field(result, field.name) = &list.toOwnedSlice()[0];
                                } else {
                                    // TODO: Recover memory?
                                    @field(result, field.name) = null;
                                }
                            } else {
                                // TODO: Recover memory
                                @field(result, field.name) = list.toOwnedSlice()[0];
                            }
                        } else {
                            @field(result, field.name) = list.toOwnedSlice();
                        }
                    }
                    return FieldResultUnion{ .Success = {} };
                }

                pub fn _parse(allocator: *std.mem.Allocator, stream: Stream, from: usize) error{OutOfMemory}!InternalParseUnion(Into) {
                    var result: Into = undefined;
                    var consumed: usize = 0;
                    // TODO: Use a bump-allocator that doesn't require recursive deallocation.

                    inline for (fields) |field| {
                        const r = try @noInlineCall(@This()._parseField, field, &result, stream, from, &consumed, allocator);
                        const Tags = @TagType(@typeOf(r));
                        const tag = Tags(r);
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
                    result.location = stream.locations[from].span(stream.locations[from + consumed]);
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
        pub const fluent = Fluent{ .fields = [_]Field{} };
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
        .tokens = [_]Token{Token{ .A = {} }},
        .locations = [_]Location{ undefined, undefined },
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
            return comb.Stream{ .tokens = tokens.toOwnedSlice(), .locations = locations.toOwnedSlice() };
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

    var parse_error: ParseErrorMessage = undefined;

    const stdout_file = try std.io.getStdOut();
    const result = AST.Phrase.Parser.parse(allocator, stream, &parse_error) catch |err| switch (err) {
        error.ParseError => |e| {
            try parse_error.render(stdout_file);
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
