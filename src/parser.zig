// parser.zig:
// A generic parsing library for building recursive descent grammars out of
// parsing combinators.

const std = @import("std");
const assert = std.debug.assert;
const ArrayList = std.ArrayList;

////////////////////////////////////////////////////////////////////////////////

/// Source: https://github.com/ziglang/zig/blob/987c209b407f8379fd58381dcd3975982dfccdaf/std/io.zig#L1181
/// TODO: Replace this with @unionInit (https://github.com/ziglang/zig/issues/1315)
fn setTag(ptr: var, tag: var) void {
    const T = @typeOf(ptr);
    const U = std.meta.Child(T);

    const info = @typeInfo(U).Union;
    if (info.tag_type) |TagType| {
        comptime assert(TagType == @typeOf(tag));

        var ptr_tag = ptr: {
            if (@alignOf(TagType) >= @alignOf(U)) break :ptr @ptrCast(*TagType, ptr);
            const offset = comptime max: {
                var max_field_size: comptime_int = 0;
                for (info.fields) |field_info| {
                    const field_size = @sizeOf(field_info.field_type);
                    max_field_size = std.math.max(max_field_size, field_size);
                }
                break :max std.math.max(max_field_size, @alignOf(U));
            };
            break :ptr @intToPtr(*TagType, @ptrToInt(ptr) + offset);
        };
        ptr_tag.* = tag;
    }
}

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
};

/// A ParseErrorMessage represents an error message produced when parsing.
pub const ParseErrorMessage = struct {
    pub const Entry = union(enum) {
        Text: []const u8,
        AtLocation: Location,
    };

    entries: []const Entry,
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
            /// A negative maximum take means no limit.
            max_take_count: isize,

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

            fn _type(comptime field: Field) type {
                if (field.max_take_count == 1) {
                    if (field.min_take_count == 0) {
                        return ?field.CT;
                    }
                    return field.CT;
                } else {
                    return []const field.CT;
                }
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

        fn InternalParseResult(comptime T: type) type {
            return struct {
                value: T,
                consumed: usize,
            };
        }

        pub fn TokenParser(comptime Into: type, comptime pattern: @TagType(Token)) type {
            return struct {
                pub fn deinit(allocator: *std.mem.Allocator, self: Into) void {}

                pub fn _parse(allocator: *std.mem.Allocator, stream: Stream, from: usize, parse_error: *ParseErrorMessage) InternalParseErrors!InternalParseResult(Into) {
                    if (stream.tokens.len == from) {
                        return error.NoMatch;
                    }
                    const head = stream.tokens[from];
                    switch (stream.tokens[from]) {
                        pattern => |value| return InternalParseResult(Into){
                            .consumed = 1,
                            .value = Into{
                                .value = value,
                                .location = stream.locations[from],
                            },
                        },
                        else => return error.NoMatch,
                    }
                }
            };
        }

        pub fn ChoiceParser(comptime Into: type) type {
            return struct {
                pub fn deinit(allocator: *std.mem.Allocator, self: Into) void {
                    const TagType = @TagType(Into);
                    inline for (std.meta.fields(Into)) |field| {
                        if (@enumToInt(TagType(self)) == field.enum_field.?.value) {
                            var subvalue = @field(self, field.name);
                            @typeOf(subvalue.*).Parser.deinit(allocator, subvalue.*);
                            allocator.destroy(@field(self, field.name));
                        }
                    }
                }

                pub fn _parse(allocator: *std.mem.Allocator, stream: Stream, from: usize, parse_error: *ParseErrorMessage) InternalParseErrors!InternalParseResult(Into) {
                    @setRuntimeSafety(false);
                    inline for (std.meta.fields(Into)) |field| {
                        const FieldType = @typeInfo(field.field_type).Pointer.child;
                        if (FieldType.Parser._parse(allocator, stream, from, parse_error)) |result| {
                            var field_value = try allocator.create(FieldType);
                            field_value.* = result.value;

                            // TODO: Remove setRuntimeSafety(false); Blocked by https://github.com/ziglang/zig/issues/1315
                            var choice: Into = undefined;
                            {
                                setTag(&choice, @field(Into, field.name));
                                @field(choice, field.name) = field_value;
                            }
                            return InternalParseResult(Into){
                                .value = choice,
                                .consumed = result.consumed,
                            };
                        } else |err| switch (err) {
                            error.NoMatch => {},
                            error.ParseError => return error.ParseError,
                            error.OutOfMemory => return error.OutOfMemory,
                        }
                    }
                    return error.NoMatch;
                }
            };
        }

        pub fn SequenceParser(comptime Into: type, comptime fields: []const Field) type {
            return struct {
                pub fn _deinitFirst(allocator: *std.mem.Allocator, self: Into, first: usize) void {
                    inline for (fields) |field, i| {
                        if (i < first) {
                            if (comptime !std.mem.eql(u8, "_", field.name)) {
                                const field_value = @field(self, field.name);
                                if (field.max_take_count == 1) {
                                    if (field.min_take_count == 0) {
                                        if (field_value) |present| {
                                            field.CT.Parser.deinit(allocator, present);
                                        }
                                    } else {
                                        field.CT.Parser.deinit(allocator, field_value);
                                    }
                                } else {
                                    for (field_value) |element| {
                                        field.CT.Parser.deinit(allocator, element);
                                    }
                                    allocator.free(field_value);
                                }
                            }
                        }
                    }
                }

                pub fn deinit(allocator: *std.mem.Allocator, self: Into) void {
                    @This()._deinitFirst(allocator, self, fields.len);
                }

                pub fn parse(allocator: *std.mem.Allocator, stream: Stream, parse_error: *ParseErrorMessage) ParseErrors!Into {
                    var result = @This()._parse(allocator, stream, 0, parse_error) catch |err| switch (err) {
                        error.NoMatch => {
                            var entries = try allocator.alloc(ParseErrorMessage.Entry, 2);
                            entries[0] = ParseErrorMessage.Entry{ .Text = "Expected (thing)" };
                            entries[1] = ParseErrorMessage.Entry{ .AtLocation = stream.locations[0] };
                            parse_error.* = ParseErrorMessage{ .entries = entries };
                            return error.ParseError;
                        },
                        error.ParseError => return error.ParseError,
                        error.OutOfMemory => return error.OutOfMemory,
                    };

                    if (result.consumed != stream.tokens.len) {
                        var entries = try allocator.alloc(ParseErrorMessage.Entry, 2);
                        entries[0] = ParseErrorMessage.Entry{ .Text = "Unexpected end to (thing)" };
                        entries[1] = ParseErrorMessage.Entry{ .AtLocation = stream.locations[result.consumed] };
                        parse_error.* = ParseErrorMessage{ .entries = entries };
                        return error.ParseError;
                    }
                    return result.value;
                }

                pub fn _parse(allocator: *std.mem.Allocator, stream: Stream, from: usize, parse_error: *ParseErrorMessage) InternalParseErrors!InternalParseResult(Into) {
                    var result: Into = undefined;
                    var consumed: usize = 0;
                    var progress: usize = 0;
                    errdefer {
                        // TODO: Use a bump-allocator that doesn't require recursive deallocation.
                        @This()._deinitFirst(allocator, result, progress);
                    }

                    inline for (fields) |field, fi| {
                        var subAST: field._type() = undefined;
                        // Parse the field.
                        if (field.max_take_count == 1) {
                            // Parse a required/optional field.
                            if (field.CT.Parser._parse(allocator, stream, from + consumed, parse_error)) |subresult| {
                                subAST = subresult.value;
                                consumed += subresult.consumed;
                            } else |err| switch (err) {
                                error.NoMatch => {
                                    if (field.min_take_count == 0) {
                                        subAST = null;
                                    } else {
                                        if (field.cut_message) |cut_message| {
                                            var entries = try allocator.alloc(ParseErrorMessage.Entry, 2);
                                            entries[0] = ParseErrorMessage.Entry{ .Text = cut_message };
                                            entries[1] = ParseErrorMessage.Entry{ .AtLocation = stream.locations[from + consumed] };
                                            parse_error.* = ParseErrorMessage{ .entries = entries };
                                            return error.ParseError;
                                        }
                                        return error.NoMatch;
                                    }
                                },
                                error.ParseError => {
                                    return InternalParseErrors.ParseError;
                                },
                                error.OutOfMemory => {
                                    return err;
                                },
                            }
                        } else {
                            // Parse a repeated field.
                            var list = std.ArrayList(field.CT).init(allocator);
                            while (true) {
                                // Parse a separator, if any.
                                if (field.separator) |sep| {
                                    if (list.count() != 0) {
                                        if (sep.Parser._parse(allocator, stream, from + consumed, parse_error)) |subresult| {
                                            sep.Parser.deinit(allocator, subresult.value);
                                            consumed += subresult.consumed;
                                        } else |err| switch (err) {
                                            error.NoMatch => {
                                                break;
                                            },
                                            error.ParseError => {
                                                return err;
                                            },
                                            error.OutOfMemory => {
                                                return err;
                                            },
                                        }
                                    }
                                }

                                // Parse an element in the list.
                                if (field.CT.Parser._parse(allocator, stream, from + consumed, parse_error)) |subresult| {
                                    try list.append(subresult.value);
                                    consumed += subresult.consumed;
                                } else |err| switch (err) {
                                    error.NoMatch => {
                                        break;
                                    },
                                    error.ParseError => {
                                        return err;
                                    },
                                    error.OutOfMemory => {
                                        return err;
                                    },
                                }

                                assert(field.separator == null);
                            }

                            if (list.count() < field.min_take_count) {
                                if (field.cut_message) |cut_message| {
                                    var entries = try allocator.alloc(ParseErrorMessage.Entry, 2);
                                    entries[0] = ParseErrorMessage.Entry{ .Text = cut_message };
                                    entries[1] = ParseErrorMessage.Entry{ .AtLocation = stream.locations[from + consumed] };
                                    parse_error.* = ParseErrorMessage{ .entries = entries };
                                    return error.ParseError;
                                }
                                return error.NoMatch;
                            }
                            subAST = list.toOwnedSlice();
                        }

                        // Attach the sub-result onto the AST.
                        if (comptime std.mem.eql(u8, "_", field.name)) {
                            assert(field.max_take_count == 1);
                            field.CT.Parser.deinit(allocator, subAST);
                        } else {
                            @field(result, field.name) = subAST;
                        }
                        progress = fi + 1;
                    }

                    // Produce the finished result, including Location annotations.
                    result.location = stream.locations[from].span(stream.locations[from + consumed]);
                    return InternalParseResult(Into){
                        .consumed = consumed,
                        .value = result,
                    };
                }
            };
        }

        /// The `fluent` instance is the start for the Fluent interface.
        pub const fluent = Fluent{ .fields = [_]Field{} };
    };
}
