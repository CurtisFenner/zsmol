// grammar.zig:
// Defines the grammar of Smol using a parser combinator library.

const std = @import("std");
const assert = std.debug.assert;
const ArrayList = std.ArrayList;

const parser = @import("parser.zig");

pub const Blob = parser.Blob;
pub const Location = parser.Location;
pub const ErrorMessage = parser.ErrorMessage;
const Identifier = @import("identifiers.zig").Identifier;
const IdentifierPool = @import("identifiers.zig").IdentifierPool;

////////////////////////////////////////////////////////////////////////////////

const comb = parser.Combinators(Token);

pub const Operators = enum {
    Concat,
    Difference,
    Eq,
    LessThan,
    Mod,
    Product,
    Quotient,
    Sum,
};

pub const Token = union(enum) {
    Iden: Identifier,
    TypeIden: Identifier,

    // Does NOT include the `#`.
    TypeVar: Identifier,

    // Contains the sequence of bytes *described* by the string,
    // rather than the literal contents of the string literal
    // (ie., the literal `"\n"` becomes the slice `[1]u8{10}`.
    StringLiteral: []const u8,

    IntLiteral: i64,

    KeyAssert: void,
    KeyCase: void,
    KeyClass: void,
    KeyDo: void,
    KeyElse: void,
    KeyElseif: void,
    KeyEnsures: void,
    KeyFalse: void,
    KeyForall: void,
    KeyIf: void,
    KeyImport: void,
    KeyInterface: void,
    KeyIs: void,
    KeyIsa: void,
    KeyMatch: void,
    KeyMethod: void,
    KeyNew: void,
    KeyPackage: void,
    KeyRequires: void,
    KeyReturn: void,
    KeyFn: void,
    KeyThis: void,
    KeyTrue: void,
    KeyUnion: void,
    KeyUnit: void,
    KeyVar: void,
    KeyWhen: void,

    TypeBoolean: void,
    TypeInt: void,
    TypeSelf: void,
    TypeString: void,
    TypeUnit: void,

    // Reserved, but unused:
    KeyAsync: void,
    KeyAwait: void,
    KeyBreak: void,
    KeyEnum: void,
    KeyForeign: void,
    KeyFor: void,
    KeyFunction: void,
    KeyOf: void,
    KeyRecord: void,
    KeyResource: void,
    KeyResume: void,
    KeyService: void,
    KeyType: void,
    KeyTest: void,
    KeyUntil: void,
    KeyWhile: void,
    KeyYield: void,
    TypeNever: void,
    TypeThis: void,

    PuncAssign: void,
    Operator: Operators,

    PuncDot: void,
    PuncComma: void,
    PuncColon: void,
    PuncSemicolon: void,
    PuncBang: void,
    PuncQuery: void,
    PuncBar: void,
    PuncRoundOpen: void,
    PuncRoundClose: void,
    PuncSquareOpen: void,
    PuncSquareClose: void,
    PuncCurlyOpen: void,
    PuncCurlyClose: void,

    fn deinit(self: Token, allocator: *std.mem.Allocator) void {
        switch (self) {
            .StringLiteral => |sl| {
                allocator.free(sl);
            },
            else => {},
        }
    }
};

const KeywordPattern = struct {
    word: []const u8,
    token: Token,
};

/// Multi-character operators and the assignment operator.
const operator_strs = [_]KeywordPattern{
    KeywordPattern{ .word = "=", .token = Token{ .PuncAssign = {} } },
    KeywordPattern{ .word = "++", .token = Token{ .Operator = Operators.Concat } },
    KeywordPattern{ .word = "==", .token = Token{ .Operator = Operators.Eq } },
    KeywordPattern{ .word = "<", .token = Token{ .Operator = Operators.LessThan } },
    KeywordPattern{ .word = "%", .token = Token{ .Operator = Operators.Mod } },
    KeywordPattern{ .word = "*", .token = Token{ .Operator = Operators.Product } },
    KeywordPattern{ .word = "/", .token = Token{ .Operator = Operators.Quotient } },
    KeywordPattern{ .word = "+", .token = Token{ .Operator = Operators.Sum } },
};

/// Single-character punctuation marks.
const punctuation_strs = [_]KeywordPattern{
    KeywordPattern{ .word = ".", .token = Token{ .PuncDot = {} } },
    KeywordPattern{ .word = ",", .token = Token{ .PuncComma = {} } },
    KeywordPattern{ .word = ":", .token = Token{ .PuncColon = {} } },
    KeywordPattern{ .word = ";", .token = Token{ .PuncSemicolon = {} } },
    KeywordPattern{ .word = "!", .token = Token{ .PuncBang = {} } },
    KeywordPattern{ .word = "?", .token = Token{ .PuncQuery = {} } },
    KeywordPattern{ .word = "|", .token = Token{ .PuncBar = {} } },
    KeywordPattern{ .word = "(", .token = Token{ .PuncRoundOpen = {} } },
    KeywordPattern{ .word = ")", .token = Token{ .PuncRoundClose = {} } },
    KeywordPattern{ .word = "[", .token = Token{ .PuncSquareOpen = {} } },
    KeywordPattern{ .word = "]", .token = Token{ .PuncSquareClose = {} } },
    KeywordPattern{ .word = "{", .token = Token{ .PuncCurlyOpen = {} } },
    KeywordPattern{ .word = "}", .token = Token{ .PuncCurlyClose = {} } },
};

/// Keywords beginning with an uppercase letter.
const type_keyword_strs = [_]KeywordPattern{
    KeywordPattern{ .word = "Unit", .token = Token{ .TypeUnit = {} } },
    KeywordPattern{ .word = "Boolean", .token = Token{ .TypeBoolean = {} } },
    KeywordPattern{ .word = "Int", .token = Token{ .TypeInt = {} } },
    KeywordPattern{ .word = "String", .token = Token{ .TypeString = {} } },

    // Reserved, but unused:
    KeywordPattern{ .word = "Never", .token = Token{ .TypeNever = {} } },
    KeywordPattern{ .word = "This", .token = Token{ .TypeThis = {} } },
};

/// Keywords beginning with a lowercase letter
const keyword_strs = [_]KeywordPattern{
    KeywordPattern{ .word = "assert", .token = Token{ .KeyAssert = {} } },
    KeywordPattern{ .word = "case", .token = Token{ .KeyCase = {} } },
    KeywordPattern{ .word = "class", .token = Token{ .KeyClass = {} } },
    KeywordPattern{ .word = "do", .token = Token{ .KeyDo = {} } },
    KeywordPattern{ .word = "else", .token = Token{ .KeyElse = {} } },
    KeywordPattern{ .word = "elseif", .token = Token{ .KeyElseif = {} } },
    KeywordPattern{ .word = "ensures", .token = Token{ .KeyEnsures = {} } },
    KeywordPattern{ .word = "false", .token = Token{ .KeyFalse = {} } },
    KeywordPattern{ .word = "fn", .token = Token{ .KeyFn = {} } },
    KeywordPattern{ .word = "forall", .token = Token{ .KeyForall = {} } },
    KeywordPattern{ .word = "foreign", .token = Token{ .KeyForeign = {} } },
    KeywordPattern{ .word = "if", .token = Token{ .KeyIf = {} } },
    KeywordPattern{ .word = "import", .token = Token{ .KeyImport = {} } },
    KeywordPattern{ .word = "interface", .token = Token{ .KeyInterface = {} } },
    KeywordPattern{ .word = "is", .token = Token{ .KeyIs = {} } },
    KeywordPattern{ .word = "isa", .token = Token{ .KeyIsa = {} } },
    KeywordPattern{ .word = "match", .token = Token{ .KeyMatch = {} } },
    KeywordPattern{ .word = "method", .token = Token{ .KeyMethod = {} } },
    KeywordPattern{ .word = "new", .token = Token{ .KeyNew = {} } },
    KeywordPattern{ .word = "package", .token = Token{ .KeyPackage = {} } },
    KeywordPattern{ .word = "requires", .token = Token{ .KeyRequires = {} } },
    KeywordPattern{ .word = "return", .token = Token{ .KeyReturn = {} } },
    KeywordPattern{ .word = "this", .token = Token{ .KeyThis = {} } },
    KeywordPattern{ .word = "true", .token = Token{ .KeyTrue = {} } },
    KeywordPattern{ .word = "union", .token = Token{ .KeyUnion = {} } },
    KeywordPattern{ .word = "unit", .token = Token{ .KeyUnit = {} } },
    KeywordPattern{ .word = "var", .token = Token{ .KeyVar = {} } },
    KeywordPattern{ .word = "when", .token = Token{ .KeyWhen = {} } },

    // Reserved, but unused:
    KeywordPattern{ .word = "async", .token = Token{ .KeyAsync = {} } },
    KeywordPattern{ .word = "await", .token = Token{ .KeyAwait = {} } },
    KeywordPattern{ .word = "break", .token = Token{ .KeyBreak = {} } },
    KeywordPattern{ .word = "enum", .token = Token{ .KeyEnum = {} } },
    KeywordPattern{ .word = "for", .token = Token{ .KeyFor = {} } },
    KeywordPattern{ .word = "function", .token = Token{ .KeyFunction = {} } },
    KeywordPattern{ .word = "of", .token = Token{ .KeyOf = {} } },
    KeywordPattern{ .word = "record", .token = Token{ .KeyRecord = {} } },
    KeywordPattern{ .word = "resource", .token = Token{ .KeyResource = {} } },
    KeywordPattern{ .word = "resume", .token = Token{ .KeyResume = {} } },
    KeywordPattern{ .word = "service", .token = Token{ .KeyService = {} } },
    KeywordPattern{ .word = "test", .token = Token{ .KeyTest = {} } },
    KeywordPattern{ .word = "type", .token = Token{ .KeyType = {} } },
    KeywordPattern{ .word = "until", .token = Token{ .KeyUntil = {} } },
    KeywordPattern{ .word = "while", .token = Token{ .KeyWhile = {} } },
    KeywordPattern{ .word = "yield", .token = Token{ .KeyYield = {} } },
};

fn recognizePattern(comptime patterns: []const KeywordPattern, str: []const u8) ?Token {
    inline for (patterns) |pattern| {
        if (std.mem.eql(u8, pattern.word, str)) {
            return pattern.token;
        }
    }
    return null;
}

const CharacterClass = struct {
    bits: [4]u64,

    fn empty() CharacterClass {
        return CharacterClass{ .bits = [4]u64{ 0, 0, 0, 0 } };
    }

    fn sum(a: CharacterClass, b: CharacterClass) CharacterClass {
        return CharacterClass{
            .bits = [4]u64{
                a.bits[0] | b.bits[0],
                a.bits[1] | b.bits[1],
                a.bits[2] | b.bits[2],
                a.bits[3] | b.bits[3],
            },
        };
    }

    fn fromRange(low: u8, high: u8) CharacterClass {
        var bits = [4]u64{ 0, 0, 0, 0 };
        var i = low;
        while (true) {
            var bit = @intCast(u64, 1) << @intCast(u6, i % 64);
            bits[i / 64] |= bit;
            if (i == high) {
                break;
            }
            i += 1;
        }
        return CharacterClass{ .bits = bits };
    }

    fn fromList(list: []const u8) CharacterClass {
        var bits = [4]u64{ 0, 0, 0, 0 };
        for (list) |c| {
            var bit = @intCast(u64, 1) << @intCast(u6, c % 64);
            bits[c / 64] |= bit;
        }
        return CharacterClass{ .bits = bits };
    }

    fn contains(c: CharacterClass, x: u8) bool {
        return (c.bits[x / 64] >> @intCast(u6, x % 64)) & 1 != 0;
    }

    fn match(class: CharacterClass, text: []const u8) usize {
        for (text) |c, i| {
            if (!class.contains(c)) {
                return i;
            }
        }
        return text.len;
    }
};

test "a in CharacterClass.fromRange('a', 'z')" {
    assert(CharacterClass.fromRange('a', 'z').contains('a'));
}
test "b in CharacterClass.fromRange('a', 'z')" {
    assert(CharacterClass.fromRange('a', 'z').contains('b'));
}
test "z in CharacterClass.fromRange('a', 'z')" {
    assert(CharacterClass.fromRange('a', 'z').contains('z'));
}
test "` not in CharacterClass.fromRange('a', 'z')" {
    assert(!CharacterClass.fromRange('a', 'z').contains('`'));
}
test "{ not in CharacterClass.fromRange('a', 'z')" {
    assert(!CharacterClass.fromRange('a', 'z').contains('{'));
}

const TokenizeResult = struct {
    consumed: usize,
    token: ?Token,
};

const lowercase_class = CharacterClass.fromRange('a', 'z');
const uppercase_class = CharacterClass.fromRange('A', 'Z');
const digit_class = CharacterClass.fromRange('0', '9');
const identifier_class = lowercase_class.sum(uppercase_class).sum(digit_class);

fn parseTypeVariable(identifier_pool: *IdentifierPool, blob: *const parser.Blob, from: usize, compile_error: *ErrorMessage) !TokenizeResult {
    const stop = identifier_class.match(blob.content[from + 1 ..]);
    const name = blob.content[from + 1 .. from + 1 + stop];
    if (stop == 0 or !uppercase_class.contains(name[0])) {
        const location = Location{ .blob = blob, .begin = from, .end = from + 1 };
        compile_error.* = parser.makeParseError(location, "Malformed type variable");
    }

    const token = if (std.mem.eql(u8, "Self", name)) Token{ .TypeSelf = {} } else Token{ .TypeVar = try identifier_pool.add(name) };
    return TokenizeResult{
        .consumed = stop + 1,
        .token = token,
    };
}

fn parseIntLiteral(blob: *const parser.Blob, from: usize, compile_error: *ErrorMessage) !TokenizeResult {
    const lowercase = CharacterClass.fromRange('a', 'z');
    const uppercase = CharacterClass.fromRange('A', 'Z');
    const digits = CharacterClass.fromRange('0', '9');
    const underscore = CharacterClass.fromList("_");

    // Find the stop of this "word".
    const stop = lowercase.sum(uppercase).sum(digits).sum(underscore).match(blob.content[from..]);

    // TODO: Allow underscores in literals (e.g., `1_000_000`).
    const check = digits.match(blob.content[from..]);

    const value = std.fmt.parseInt(i64, blob.content[from .. from + stop], 10) catch |err| switch (err) {
        error.Overflow, error.InvalidCharacter => {
            const location = Location{ .blob = blob, .begin = from, .end = from + stop };
            compile_error.* = parser.makeParseError(location, "Malformed number literal");
            return error.ParseError;
        },
    };
    return TokenizeResult{
        .consumed = stop,
        .token = Token{ .IntLiteral = value },
    };
}

fn parseStringLiteral(allocator: *std.mem.Allocator, blob: *const parser.Blob, from: usize, compile_error: *ErrorMessage) !TokenizeResult {
    // TODO: Avoid multiple allocations by doing two passes.
    var storage = std.ArrayList(u8).init(allocator);
    errdefer storage.deinit();

    var i: usize = 1;
    var escaped: bool = false;
    while (true) {
        if (from + i == blob.content.len or blob.content[from + i] == '\n') {
            compile_error.* = ErrorMessage.make(&[_]ErrorMessage.Entry{
                .{ .Text = "Unfinished string literal" },
                .{
                    .AtLocation = Location{
                        .blob = blob,
                        .begin = from,
                        .end = from + i,
                    },
                },
            });
            return error.ParseError;
        }

        var at = blob.content[from + i];
        if (escaped) {
            if (at == '\\') {
                try storage.append('\\');
            } else if (at == '\n') {
                try storage.append('\n');
            } else if (at == '"') {
                try storage.append('"');
            } else {
                compile_error.* = ErrorMessage.make(&[_]ErrorMessage.Entry{
                    .{ .Text = "Invalid escape sequence used" },
                    .{
                        .AtLocation = Location{
                            .blob = blob,
                            .begin = from + i - 1,
                            .end = from + i + 1,
                        },
                    },
                });
                return error.ParseError;
            }
            escaped = false;
        } else {
            if (at == '\\') {
                escaped = true;
            } else if (at == '"') {
                return TokenizeResult{
                    .consumed = i + 1,
                    .token = Token{ .StringLiteral = storage.toOwnedSlice() },
                };
            } else if (32 <= at and at <= 127) {
                try storage.append(at);
            } else {
                compile_error.* = ErrorMessage.make(&[_]ErrorMessage.Entry{
                    .{ .Text = "Invalid string literal byte" },
                    .{
                        .AtLocation = Location{
                            .blob = blob,
                            .begin = from + i,
                            .end = from + i + 1,
                        },
                    },
                });
                return error.ParseError;
            }
        }

        i += 1;
    }
}

/// When returning a ParseError, writes a message to compile_error.
fn parseToken(allocator: *std.mem.Allocator, identifier_pool: *IdentifierPool, blob: *const parser.Blob, from: usize, compile_error: *ErrorMessage) !TokenizeResult {
    assert(from < blob.content.len);

    const space_class = CharacterClass.fromList(&[_]u8{ ' ', '\t', '\n' });
    const operator_class = CharacterClass.fromList(&[_]u8{ '=', '<', '+', '-', '*', '/', '%' });
    const comment_body_class = CharacterClass.fromRange(32, 127);

    const remaining = blob.content.len - from;
    const at = blob.content[from];
    if (space_class.contains(at)) {
        return TokenizeResult{ .consumed = 1, .token = null };
    } else if ('a' <= at and at <= 'z') {
        // Parse an Iden or a keyword.
        const matching = identifier_class.match(blob.content[from..]);
        const word = blob.content[from .. from + matching];
        return TokenizeResult{
            .consumed = matching,
            .token = recognizePattern(&keyword_strs, word) orelse Token{ .Iden = try identifier_pool.add(word) },
        };
    } else if ('A' <= at and at <= 'Z') {
        // Parse a TypeIden or a keyword.
        const matching = identifier_class.match(blob.content[from..]);
        const word = blob.content[from .. from + matching];
        return TokenizeResult{
            .consumed = matching,
            .token = recognizePattern(&type_keyword_strs, word) orelse Token{ .TypeIden = try identifier_pool.add(word) },
        };
    } else if (recognizePattern(&punctuation_strs, blob.content[from .. from + 1])) |p| {
        return TokenizeResult{
            .consumed = 1,
            .token = p,
        };
    } else if (operator_class.contains(at)) {
        const matching = operator_class.match(blob.content[from..]);
        if (matching >= 2 and blob.content[from] == '/' and blob.content[from + 1] == '/') {
            // Parse a single-line `//` comment.
            const comment_end = comment_body_class.match(blob.content[from + 2 ..]);
            return TokenizeResult{ .consumed = 2 + comment_end, .token = null };
        } else if (matching > 2) {
            compile_error.* = ErrorMessage.make(&[_]ErrorMessage.Entry{
                .{ .Text = "Unknown operator" },
                .{ .AtLocation = Location{ .blob = blob, .begin = from, .end = from + matching } },
            });
            return error.ParseError;
        }
        const op = blob.content[from .. from + matching];
        if (recognizePattern(&operator_strs, op)) |op_token| {
            return TokenizeResult{ .consumed = op.len, .token = op_token };
        }
    } else if ('0' <= at and at <= '9') {
        return parseIntLiteral(blob, from, compile_error);
    } else if ('#' == at) {
        return parseTypeVariable(identifier_pool, blob, from, compile_error);
    } else if (at == '"') {
        return parseStringLiteral(allocator, blob, from, compile_error);
    }

    compile_error.* = ErrorMessage.make(&[_]ErrorMessage.Entry{
        .{ .Text = "Unrecognized token" },
        .{
            .AtLocation = Location{
                .blob = blob,
                .begin = from,
                .end = from + 1,
            },
        },
    });
    return error.ParseError;
}

/// RETURNS a stream of tokens for the given blob.
pub fn tokenize(allocator: *std.mem.Allocator, identifier_pool: *IdentifierPool, blob: *const parser.Blob, compile_error: *parser.ErrorMessage) !comb.Stream {
    var tokens = ArrayList(Token).init(allocator);
    errdefer tokens.deinit();
    var locations = ArrayList(Location).init(allocator);
    errdefer locations.deinit();

    var from: usize = 0;
    while (from < blob.content.len) {
        const result = try parseToken(allocator, identifier_pool, blob, from, compile_error);
        assert(result.consumed != 0);
        if (result.token) |token| {
            try tokens.append(token);
            try locations.append(Location{
                .blob = blob,
                .begin = from,
                .end = from + result.consumed,
            });
        }
        from += result.consumed;
    }

    try locations.append(Location{
        .blob = blob,
        .begin = blob.content.len,
        .end = blob.content.len,
    });

    return comb.Stream{
        .allocator = allocator,
        .tokens = tokens.toOwnedSlice(),
        .locations = locations.toOwnedSlice(),
    };
}

test "Tokenize `alpha`" {
    const blob = Blob{
        .name = "test",
        .content = "alpha",
    };
    var compile_error: ErrorMessage = undefined;
    var identifier_pool = IdentifierPool.init(std.testing.allocator);
    defer identifier_pool.deinit();
    const stream = try tokenize(std.testing.allocator, &identifier_pool, &blob, &compile_error);
    defer stream.deinit();
    assert(stream.tokens.len == 1);
    assert(stream.locations.len == 2);
    assert(stream.locations[0].begin == 0);
    assert(stream.locations[0].end == 5);
    assert(stream.locations[1].begin == 5);
    assert(stream.locations[1].end == 5);
    assert(stream.tokens[0].Iden.eq(identifier_pool.get("alpha").?));
}

test "Tokenize `alpha.beta`" {
    const blob = Blob{
        .name = "test",
        .content = "alpha.beta",
    };
    var compile_error: ErrorMessage = undefined;
    var identifier_pool = IdentifierPool.init(std.testing.allocator);
    defer identifier_pool.deinit();
    const stream = try tokenize(std.testing.allocator, &identifier_pool, &blob, &compile_error);
    defer stream.deinit();
    assert(stream.tokens.len == 3);
    assert(stream.locations.len == 4);
    assert(stream.locations[0].begin == 0);
    assert(stream.locations[0].end == 5);
    assert(stream.locations[1].begin == 5);
    assert(stream.locations[1].end == 6);
    assert(stream.locations[2].begin == 6);
    assert(stream.locations[2].end == 10);
    assert(stream.locations[3].begin == 10);
    assert(stream.locations[3].end == 10);
    assert(stream.tokens[0].Iden.eq(identifier_pool.get("alpha").?));
    switch (stream.tokens[1]) {
        .PuncDot => {},
        else => unreachable,
    }
    assert(stream.tokens[2].Iden.eq(identifier_pool.get("beta").?));
}

test "Tokenize `if`" {
    const blob = Blob{
        .name = "test",
        .content = "if",
    };
    var compile_error: ErrorMessage = undefined;
    var identifier_pool = IdentifierPool.init(std.testing.allocator);
    defer identifier_pool.deinit();
    const stream = try tokenize(std.testing.allocator, &identifier_pool, &blob, &compile_error);
    defer stream.deinit();
    assert(stream.tokens.len == 1);
    assert(stream.locations.len == 2);
    assert(stream.locations[0].begin == 0);
    assert(stream.locations[0].end == 2);
    assert(stream.locations[1].begin == 2);
    assert(stream.locations[1].end == 2);
    switch (stream.tokens[0]) {
        .KeyIf => {},
        else => unreachable,
    }
}

////////////////////////////////////////////////////////////////////////////////

/// Parses the given Blob as a Smol source file.
/// When this function returns a ParseError, the error is written to the
/// compile_error parameter.
pub fn parseSource(allocator: *std.mem.Allocator, identifier_pool: *IdentifierPool, blob: *const Blob, compile_error: *ErrorMessage) !Source {
    const stream = try tokenize(allocator, identifier_pool, blob, compile_error);
    const source = try Source.Parser.parse(allocator, stream, compile_error);
    return source;
}

////////////////////////////////////////////////////////////////////////////////

pub fn Leaf(comptime name: []const u8) type {
    return struct {
        value: std.meta.TagPayloadType(Token, @field(Token, name)),
        location: Location,
        pub const Parser = comb.TokenParser(@This(), @field(Token, name));
    };
}

test "leaf" {
    const a = LeafTypeVar;
    // a.Parser.parse();
}

pub const LeafIden = Leaf("Iden");
pub const LeafIntLiteral = Leaf("IntLiteral");
pub const LeafKeyAssert = Leaf("KeyAssert");
pub const LeafKeyCase = Leaf("KeyCase");
pub const LeafKeyClass = Leaf("KeyClass");
pub const LeafKeyDo = Leaf("KeyDo");
pub const LeafKeyElse = Leaf("KeyElse");
pub const LeafKeyElseif = Leaf("KeyElseif");
pub const LeafKeyEnsures = Leaf("KeyEnsures");
pub const LeafKeyFalse = Leaf("KeyFalse");
pub const LeafKeyFn = Leaf("KeyFn");
pub const LeafKeyForall = Leaf("KeyForall");
pub const LeafKeyIf = Leaf("KeyIf");
pub const LeafKeyImport = Leaf("KeyImport");
pub const LeafKeyInterface = Leaf("KeyInterface");
pub const LeafKeyIs = Leaf("KeyIs");
pub const LeafKeyIsa = Leaf("KeyIsa");
pub const LeafKeyMatch = Leaf("KeyMatch");
pub const LeafKeyMethod = Leaf("KeyMethod");
pub const LeafKeyNew = Leaf("KeyNew");
pub const LeafKeyPackage = Leaf("KeyPackage");
pub const LeafKeyRequires = Leaf("KeyRequires");
pub const LeafKeyReturn = Leaf("KeyReturn");
pub const LeafKeyThis = Leaf("KeyThis");
pub const LeafKeyTrue = Leaf("KeyTrue");
pub const LeafKeyUnion = Leaf("KeyUnion");
pub const LeafKeyVar = Leaf("KeyVar");
pub const LeafKeyWhen = Leaf("KeyWhen");
pub const LeafOperator = Leaf("Operator");
pub const LeafPuncAssign = Leaf("PuncAssign");
pub const LeafPuncBang = Leaf("PuncBang");
pub const LeafPuncBar = Leaf("PuncBar");
pub const LeafPuncColon = Leaf("PuncColon");
pub const LeafPuncComma = Leaf("PuncComma");
pub const LeafPuncCurlyClose = Leaf("PuncCurlyClose");
pub const LeafPuncCurlyOpen = Leaf("PuncCurlyOpen");
pub const LeafPuncDot = Leaf("PuncDot");
pub const LeafPuncRoundClose = Leaf("PuncRoundClose");
pub const LeafPuncRoundOpen = Leaf("PuncRoundOpen");
pub const LeafPuncSemicolon = Leaf("PuncSemicolon");
pub const LeafPuncSquareClose = Leaf("PuncSquareClose");
pub const LeafPuncSquareOpen = Leaf("PuncSquareOpen");
pub const LeafStringLiteral = Leaf("StringLiteral");
pub const LeafTypeBoolean = Leaf("TypeBoolean");
pub const LeafTypeIden = Leaf("TypeIden");
pub const LeafTypeInt = Leaf("TypeInt");
pub const LeafTypeSelf = Leaf("TypeSelf");
pub const LeafTypeString = Leaf("TypeString");
pub const LeafTypeUnit = Leaf("TypeUnit");
pub const LeafTypeVar = Leaf("TypeVar");

////////////////////////////////////////////////////////////////////////////////

pub const Source = struct {
    package: PackageDef,
    imports: []const Import,
    definitions: []const Definition,

    pub const Parser = comb.fluent //
        .req("package", PackageDef) //
        .star("imports", Import) //
        .star("definitions", Definition) //
        .req("_", comb.EofParser).cut("Expected the beginning of another definition") //
        .seq(@This());
    location: Location,
};

pub const PackageDef = struct {
    package_name: LeafIden,

    pub const Parser = comb.fluent //
        .req("_", LeafKeyPackage) //
        .req("package_name", LeafIden).cut("Expected a package name") //
        .req("_", LeafPuncSemicolon).cut("Expected a `;`") //
        .seq(@This());
    location: Location,
};

pub const Import = struct {
    imported: ImportChoice,

    pub const Parser = comb.fluent //
        .req("_", LeafKeyImport) //
        .req("imported", ImportChoice).cut("Expected the name of a package or object to import") //
        .req("_", LeafPuncSemicolon).cut("Expected a `;` to finish an `import`") //
        .seq(@This());
    location: Location,
};

pub const ImportChoice = union(enum) {
    OfObject: *const ImportOfObject,
    OfPackage: *const ImportOfPackage,

    pub const Parser = comb.ChoiceParser(@This());
};

pub const ImportOfObject = struct {
    package_name: LeafIden,
    object_name: LeafTypeIden,

    pub const Parser = comb.fluent //
        .req("package_name", LeafIden) //
        .req("_", LeafPuncColon) //
        .req("object_name", LeafTypeIden) //
        .seq(@This());
    location: Location,
};

pub const ImportOfPackage = struct {
    package_name: LeafIden,

    pub const Parser = comb.fluent //
        .req("package_name", LeafIden).seq(@This());
    location: Location,
};

pub const Definition = union(enum) {
    ClassDefinition: *const ClassDefinition,
    UnionDefinition: *const UnionDefinition,
    InterfaceDefinition: *const InterfaceDefinition,

    // pub fn name(self: Definition) LeafTypeIden {
    //     switch (self) {
    //         .ClassDefinition => |c| return c.class_name,
    //         .UnionDefinition => |u| return u.union_name,
    //         .InterfaceDefinition => |i| return i.interface_name,
    //     }
    // }

    pub const Parser = comb.ChoiceParser(@This());
};

pub const ClassDefinition = struct {
    class_name: LeafTypeIden,
    generics: ?*const Generics,
    implements: ?*const Implements,
    fields: []const Field,
    members: []const FunctionDef,

    pub const Parser = comb.fluent //
        .req("_", LeafKeyClass) //
        .req("class_name", LeafTypeIden).cut("Expected a class name after `class`") //
        .opt("generics", Generics) //
        .opt("implements", Implements) //
        .req("_", LeafPuncCurlyOpen).cut("Expected a `{` to begin a class's body") //
        .star("fields", Field) //
        .star("members", FunctionDef) //
        .req("_", LeafPuncCurlyClose).cut("Expected another class member or a `}` to close a class's body") //
        .seq(@This());

    location: Location,
};

pub const UnionDefinition = struct {
    union_name: LeafTypeIden,
    generics: ?*const Generics,
    implements: ?*const Implements,
    fields: []const Field,
    members: []const FunctionDef,

    pub const Parser = comb.fluent //
        .req("_", LeafKeyUnion) //
        .req("union_name", LeafTypeIden).cut("Expected a union name after `union`") //
        .opt("generics", Generics) //
        .opt("implements", Implements) //
        .req("_", LeafPuncCurlyOpen).cut("Expected a `{` to begin a union's body") //
        .star("fields", Field) //
        .star("members", FunctionDef) //
        .req("_", LeafPuncCurlyClose).cut("Expected another union member or a `}` to close a union's body") //
        .seq(@This());
    location: Location,
};

pub const Implements = struct {
    constraints: []const Type,

    pub const Parser = comb.fluent //
        .req("_", LeafKeyIs) //
        .plusSep("constraints", Type, LeafPuncComma).cut("Expected one or more type constraints after `is`") //
        .seq(@This());
    location: Location,
};

pub const Field = struct {
    field: Variable,

    pub const Parser = comb.fluent //
        .req("_", LeafKeyVar) //
        .req("field", Variable) //
        .req("_", LeafPuncSemicolon).cut("Expected a `;` after a field") //
        .seq(@This());
    location: Location,
};

pub const InterfaceDefinition = struct {
    interface_name: LeafTypeIden,
    generics: ?*const Generics,
    members: []const InterfaceMember,

    pub const Parser = comb.fluent //
        .req("_", LeafKeyInterface) //
        .req("interface_name", LeafTypeIden).cut("Expected an interface name after `interface`") //
        .opt("generics", Generics) //
        .req("_", LeafPuncCurlyOpen).cut("Expected a `{` to begin an interface's body") //
        .star("members", InterfaceMember) //
        .req("_", LeafPuncCurlyClose).cut("Expected another interface member or a `}` to close an interface's body") //
        .seq(@This());
    location: Location,
};

pub const InterfaceMember = struct {
    signature: Signature,

    pub const Parser = comb.fluent //
        .req("signature", Signature) //
        .req("_", LeafPuncSemicolon).cut("Expected a `;` after the interface member's signature") //
        .seq(@This());
    location: Location,
};

pub const Generics = struct {
    parameters: []const LeafTypeVar,
    constraints: ?*const TypeConstraints,

    pub const Parser = comb.fluent //
        .req("_", LeafPuncSquareOpen) //
        .plusSep("parameters", LeafTypeVar, LeafPuncComma).cut("Expected one or more type variables after `[`") //
        .opt("constraints", TypeConstraints) //
        .req("_", LeafPuncSquareClose).cut("Expected a `]` to finish a type-variables block") //
        .seq(@This());
    location: Location,
};

pub const TypeConstraints = struct {
    constraints: []const TypeConstraint,

    pub const Parser = comb.fluent //
        .req("_", LeafPuncBar) //
        .plusSep("constraints", TypeConstraint, LeafPuncComma).cut("Expected a type-constraint after `|`") //
        .seq(@This());
    location: Location,
};

pub const TypeConstraint = struct {
    variable: LeafTypeVar,
    constraint: Type,

    pub const Parser = comb.fluent //
        .req("variable", LeafTypeVar) //
        .req("_", LeafKeyIs).cut("Expected `is` to make a type-constraint") //
        .req("constraint", Type).cut("Expected a constraining type after `is`") //
        .seq(@This());
    location: Location,
};

pub const Type = union(enum) {
    Boolean: *const LeafTypeBoolean,
    Int: *const LeafTypeInt,
    String: *const LeafTypeString,
    Unit: *const LeafTypeUnit,
    Self: *const LeafTypeSelf,
    Generic: *const LeafTypeVar,
    Concrete: *const ConcreteType,
    pub const Parser = comb.ChoiceParser(@This());
};

pub const ConcreteType = struct {
    qualifier: ?*const PackageQualifier,
    object: LeafTypeIden,
    // TODO: Use some kind of mapping to replace this with a plain list.
    arguments: ?*const TypeArguments,

    pub const Parser = comb.fluent //
        .opt("qualifier", PackageQualifier) //
        .req("object", LeafTypeIden) //
        .opt("arguments", TypeArguments) //
        .seq(@This());
    location: Location,
};

pub const PackageQualifier = struct {
    package: LeafIden,

    pub const Parser = comb.fluent //
        .req("package", LeafIden) //
        .req("_", LeafPuncColon) //
        .seq(@This());
    location: Location,
};

pub const TypeArguments = struct {
    arguments: []const Type,

    pub const Parser = comb.fluent //
        .req("_", LeafPuncSquareOpen) //
        .plusSep("arguments", Type, LeafPuncComma).cut("Expected a type-argument after `[`") //
        .req("_", LeafPuncSquareClose).cut("Expected a `]` to finish the type-argument list") //
        .seq(@This());
    location: Location,
};

pub const Signature = struct {
    modifier: FunctionModifier,
    name: LeafIden,
    bang: ?*const LeafPuncBang,
    parameters: []const Variable,
    return_types: []const Type,
    requires: []const Requires,
    ensures: []const Ensures,

    pub const Parser = comb.fluent //
        .req("modifier", FunctionModifier) //
        .req("name", LeafIden).cut("Expected a function name after `fn`/`method`") //
        .opt("bang", LeafPuncBang) //
        .req("_", LeafPuncRoundOpen).cut("Expected a `(` to begin the function's parameters") //
        .starSep("parameters", Variable, LeafPuncComma) //
        .req("_", LeafPuncRoundClose).cut("Expected a `)` to finish the function's parameters") //
        .plusSep("return_types", Type, LeafPuncComma).cut("Expected the function's return type") //
        .star("requires", Requires) //
        .star("ensures", Ensures) //
        .seq(@This());
    location: Location,
};

pub const FunctionModifier = union(enum) {
    method: *const LeafKeyMethod,
    function: *const LeafKeyFn,
    pub const Parser = comb.ChoiceParser(@This());
};

pub const Requires = struct {
    condition: Condition,
    pub const Parser = comb.fluent //
        .req("_", LeafKeyRequires) //
        .req("condition", Condition).cut("Expected a condition after `requires`") //
        .seq(@This());
    location: Location,
};

pub const Ensures = struct {
    condition: Condition,
    pub const Parser = comb.fluent //
        .req("_", LeafKeyEnsures) //
        .req("condition", Condition).cut("Expected a condition after `ensures`") //
        .seq(@This());
    location: Location,
};

pub const Condition = struct {
    expression: Expression,
    when: ?*const ConditionWhen,
    pub const Parser = comb.fluent //
        .req("expression", Expression) //
        .opt("when", ConditionWhen) //
        .seq(@This());
    location: Location,
};

pub const ConditionWhen = struct {
    whens: []const Expression,
    pub const Parser = comb.fluent //
        .req("_", LeafKeyWhen) //
        .plusSep("whens", Expression, LeafPuncComma).cut("Expected one or more boolean expressions after `when`") //
        .seq(@This());
    location: Location,
};

pub const Variable = struct {
    v_name: LeafIden,
    v_type: Type,

    pub const Parser = comb.fluent //
        .req("v_name", LeafIden) //
        .req("v_type", Type) //
        .seq(@This());
    location: Location,
};

pub const FunctionDef = struct {
    signature: Signature,
    body: Block,

    pub const Parser = comb.fluent //
        .req("signature", Signature) //
        .req("body", Block).cut("Expected a function body after signature") //
        .seq(@This());
    location: Location,
};

pub const Block = struct {
    statements: []const Statement,

    pub const Parser = comb.fluent //
        .req("_", LeafPuncCurlyOpen) //
        .star("statements", Statement) //
        .req("_", LeafPuncCurlyClose).cut("Expected a `}` to finish a block") //
        .seq(@This());
    location: Location,
};

pub const Statement = union(enum) {
    VarSt: *const VarSt,
    DoSt: *const DoSt,
    IfSt: *const IfSt,
    MatchSt: *const MatchSt,
    AssertSt: *const AssertSt,
    ReturnSt: *const ReturnSt,
    AssignSt: *const AssignSt,

    pub const Parser = comb.ChoiceParser(@This());
};

pub const VarSt = struct {
    variables: []const Variable,
    init: []const Expression,

    pub const Parser = comb.fluent //
        .req("_", LeafKeyVar) //
        .plusSep("variables", Variable, LeafPuncComma).cut("Expected one or more variables after `var`") //
        .req("_", LeafPuncAssign).cut("Expected an `=` after variable(s)") //
        .plusSep("init", Expression, LeafPuncComma).cut("Expected an expression after `=`") //
        .req("_", LeafPuncSemicolon).cut("Expected a `;` to finish a var-statement") //
        .seq(@This());
    location: Location,
};

pub const DoSt = struct {
    expression: Expression,
    pub const Parser = comb.fluent //
        .req("_", LeafKeyDo) //
        .req("expression", Expression).cut("Expected an expression after `do`") //
        .req("_", LeafPuncSemicolon).cut("Expected a `;` to finish a do-statement") //
        .seq(@This());
    location: Location,
};

pub const IfSt = struct {
    condition: Expression,
    then_body: Block,
    elseif_clauses: []const ElseifClause,
    else_clause: ?*const ElseClause,
    pub const Parser = comb.fluent //
        .req("_", LeafKeyIf) //
        .req("condition", Expression).cut("Expected a boolean expression after `if`") //
        .req("then_body", Block).cut("Expected a then-body after an if-condition") //
        .star("elseif_clauses", ElseifClause) //
        .opt("else_clause", ElseClause) //
        .seq(@This());
    location: Location,
};

pub const ElseifClause = struct {
    condition: Expression,
    body: Block,
    pub const Parser = comb.fluent //
        .req("_", LeafKeyElseif) //
        .req("condition", Expression).cut("Expected a boolean expression after `elseif`") //
        .req("body", Block).cut("Expected an elseif-body after an elseif-condition") //
        .seq(@This());
    location: Location,
};

pub const ElseClause = struct {
    body: Block,
    pub const Parser = comb.fluent //
        .req("_", LeafKeyElse) //
        .req("body", Block).cut("Expected an else-body after `else`") //
        .seq(@This());
    location: Location,
};

pub const MatchSt = struct {
    target: Expression,
    cases: []const MatchCase,
    pub const Parser = comb.fluent //
        .req("_", LeafKeyMatch) //
        .req("target", Expression).cut("Expected a target expression after `match`") //
        .req("_", LeafPuncCurlyOpen).cut("Expected a `{` to begin a match") //
        .plus("cases", MatchCase).cut("Expected one or more match case clauses") //
        .req("_", LeafPuncCurlyClose).cut("Expected a `}` to finish a match") //
        .seq(@This());
    location: Location,
};

pub const MatchCase = struct {
    variable: LeafIden,
    body: Block,
    case: LeafIden,
    pub const Parser = comb.fluent //
        .req("_", LeafKeyCase) //
        .req("variable", LeafIden).cut("Expected a variable name after `case`") //
        .req("_", LeafKeyIs).cut("Expected `is` after match variable") //
        .req("case", LeafIden).cut("Expected variant case after `is`") //
        .req("body", Block).cut("Expected a case-body after a case tag") //
        .seq(@This());
    location: Location,
};

pub const AssertSt = struct {
    condition: Condition,
    pub const Parser = comb.fluent //
        .req("_", LeafKeyAssert) //
        .req("condition", Condition).cut("Expected a condition after `assert`") //
        .req("_", LeafPuncSemicolon).cut("Expected a `;` to finish an assert-statement") //
        .seq(@This());
    location: Location,
};

pub const ReturnSt = struct {
    values: []const Expression,
    pub const Parser = comb.fluent //
        .req("_", LeafKeyReturn) //
        .starSep("values", Expression, LeafPuncComma) //
        .req("_", LeafPuncSemicolon).cut("Expected a `;` to finish a return-statement") //
        .seq(@This());
    location: Location,
};

pub const AssignSt = struct {
    vars: []const LeafIden,
    init: []const Expression,
    pub const Parser = comb.fluent //
        .plusSep("vars", LeafIden, LeafPuncComma) //
        .req("_", LeafPuncAssign).cut("Expected an `=` after assignment variables") //
        .plusSep("init", Expression, LeafPuncComma).cut("Expected one or more expressions after `=`") //
        .req("_", LeafPuncSemicolon).cut("Expected a `;` to finish an assignment-statement") //
        .seq(@This());
    location: Location,
};

pub const Expression = union(enum) {
    ChainExpr: *const ChainExpr,
    ForallExpr: *const ForallExpr,

    pub const Parser = comb.ChoiceParser(@This());
};

pub const ChainExpr = struct {
    base: ExprAtom,
    op: ?*const ExprOp,
    isa: ?*const IsaOp,

    pub const Parser = comb.fluent //
        .req("base", ExprAtom) //
        .opt("op", ExprOp) //
        .opt("isa", IsaOp) //
        .seq(@This());
    location: Location,
};

pub const ExprAtom = struct {
    base: ExprBase,
    accesses: []const ExprAccess,

    pub const Parser = comb.fluent //
        .req("base", ExprBase) //
        .star("accesses", ExprAccess) //
        .seq(@This());
    location: Location,
};

pub const ExprOp = struct {
    operator: LeafOperator,
    rhs: ExprAtom,
    pub const Parser = comb.fluent //
        .req("operator", LeafOperator) //
        .req("rhs", ExprAtom).cut("Expected an expression after an operator") //
        .seq(@This());
    location: Location,
};

pub const IsaOp = struct {
    tag: LeafIden,
    pub const Parser = comb.fluent //
        .req("_", LeafKeyIsa) //
        .req("tag", LeafIden).cut("Expected a union tag after `isa`") //
        .seq(@This());
    location: Location,
};

pub const ForallExpr = struct {
    variable: Variable,
    quantified: Expression,
    conditions: ?*const ForallIf,

    pub const Parser = comb.fluent //
        .req("_", LeafKeyForall) //
        .req("_", LeafPuncRoundOpen).cut("Expected a `(` after `forall`") //
        .req("variable", Variable).cut("Expected a variable in a `forall` quantifier") //
        .req("_", LeafPuncRoundClose).cut("Expected a `)` to finish quantified variables list") //
        .req("quantified", Expression).cut("Expected a quantified expression") //
        .opt("conditions", ForallIf) //
        .seq(@This());
    location: Location,
};

pub const ForallIf = struct {
    conditions: []const Expression,
    pub const Parser = comb.fluent //
        .req("_", LeafKeyIf) //
        .plusSep("conditions", Expression, LeafPuncComma).cut("Expected a boolean expression") //
        .seq(@This());
    location: Location,
};

pub const ExprAccess = union(enum) {
    method: *const MethodAccess,
    field: *const FieldAccess,

    pub const Parser = comb.ChoiceParser(@This());
};

pub const MethodAccess = struct {
    m_name: LeafIden,
    bang: ?*const LeafPuncBang,
    arguments: []const Expression,

    pub const Parser = comb.fluent //
        .req("_", LeafPuncDot) //
        .req("m_name", LeafIden) //
        .opt("bang", LeafPuncBang) //
        .req("_", LeafPuncRoundOpen) //
        .starSep("arguments", Expression, LeafPuncComma) //
        .req("_", LeafPuncRoundClose).cut("Expected a `)` to finish a method call") //
        .seq(@This());
    location: Location,
};

pub const FieldAccess = struct {
    f_name: LeafIden,
    pub const Parser = comb.fluent //
        .req("_", LeafPuncDot) //
        .req("f_name", LeafIden) //
        .seq(@This());
    location: Location,
};

pub const ExprBase = union(enum) {
    Parenthesized: *const ParenExpr,
    ThisLiteral: *const LeafKeyThis,
    TrueLiteral: *const LeafKeyTrue,
    FalseLiteral: *const LeafKeyFalse,
    IntLiteral: *const LeafIntLiteral,
    StringLiteral: *const LeafStringLiteral,
    ReturnLiteral: *const LeafKeyReturn,
    StaticCall: *const StaticCallExpr,
    NewExpr: *const NewExpr,
    Variable: *const LeafIden,

    pub const Parser = comb.ChoiceParser(@This());
};

pub const ParenExpr = struct {
    expression: Expression,

    pub const Parser = comb.fluent //
        .req("_", LeafPuncRoundOpen) //
        .req("expression", Expression).cut("Expected an expression after `(`") //
        .req("_", LeafPuncRoundClose).cut("Expected a `)` to finish a parenthesized expression") //
        .seq(@This());
    location: Location,
};

pub const StaticCallExpr = struct {
    base: Type,
    f_name: LeafIden,
    bang: ?*const LeafPuncBang,
    arguments: []const Expression,
    pub const Parser = comb.fluent //
        .req("base", Type) //
        .req("_", LeafPuncDot) //
        .req("f_name", LeafIden).cut("Expected a function's name after `.`") //
        .opt("bang", LeafPuncBang) //
        .req("_", LeafPuncRoundOpen).cut("Expected a `(` to begin an argument list") //
        .starSep("arguments", Expression, LeafPuncComma) //
        .req("_", LeafPuncRoundClose).cut("Expected a `)` to finish an argument list") //
        .seq(@This());
    location: Location,
};

pub const NewExpr = struct {
    arguments: []const NamedArgument,
    pub const Parser = comb.fluent //
        .req("_", LeafKeyNew) //
        .req("_", LeafPuncRoundOpen).cut("Expected a `(` after `new`") //
        .starSep("arguments", NamedArgument, LeafPuncComma) //
        .req("_", LeafPuncRoundClose).cut("Expected a `)` to finish a new-expression") //
        .seq(@This());
    location: Location,
};

pub const NamedArgument = struct {
    name: LeafIden,
    value: Expression,
    pub const Parser = comb.fluent //
        .req("name", LeafIden) //
        .req("_", LeafPuncAssign).cut("Expected an `=` after an argument name") //
        .req("value", Expression).cut("Expected a value after `=`") //
        .seq(@This());
    location: Location,
};

////////////////////////////////////////////////////////////////////////////////

test "Parse simple variable declaration statement" {
    var blob = Blob{
        .name = "test",
        .content = "{ var vv String  = \"xyz\"; }",
    };

    var compile_error: ErrorMessage = undefined;
    var identifier_pool = IdentifierPool.init(std.testing.allocator);
    defer identifier_pool.deinit();
    const stream = try tokenize(std.testing.allocator, &identifier_pool, &blob, &compile_error);
    defer stream.deinit();

    var ast_arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer ast_arena.deinit();
    var block = Block.Parser.parse(&ast_arena.allocator, stream, &compile_error) catch |err| switch (err) {
        error.ParseError => |m| {
            try compile_error.render(std.io.getStdErr(), "");
            unreachable;
        },
        else => unreachable,
    };
    assert(block.statements.len == 1);
    const var_decl = block.statements[0];
    assert(var_decl.VarSt.variables.len == 1);
    assert(var_decl.VarSt.init.len == 1);
    assert(var_decl.VarSt.variables[0].v_name.value.eq(identifier_pool.get("vv").?));
    assert(std.mem.eql(u8, "xyz", var_decl.VarSt.init[0].ChainExpr.base.base.StringLiteral.value));
}

test "Parse simple method" {
    var blob = Blob{
        .name = "test",
        .content = "method concat(a String, b String) String { return a ++ b; }",
    };

    var compile_error: ErrorMessage = undefined;
    var identifier_pool = IdentifierPool.init(std.testing.allocator);
    defer identifier_pool.deinit();
    const stream = try tokenize(std.testing.allocator, &identifier_pool, &blob, &compile_error);
    defer stream.deinit();

    var ast_arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer ast_arena.deinit();
    var fn_def = FunctionDef.Parser.parse(&ast_arena.allocator, stream, &compile_error) catch |err| switch (err) {
        error.ParseError => |m| {
            try compile_error.render(std.io.getStdErr(), "");
            unreachable;
        },
        else => unreachable,
    };
}

test "Parse program" {
    var blob = Blob{
        .name = "test",
        .content = "package p; class M {}",
    };

    var compile_error: ErrorMessage = undefined;
    var identifier_pool = IdentifierPool.init(std.testing.allocator);
    defer identifier_pool.deinit();
    const stream = try tokenize(std.testing.allocator, &identifier_pool, &blob, &compile_error);
    defer stream.deinit();

    var ast_arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer ast_arena.deinit();
    var source = Source.Parser.parse(&ast_arena.allocator, stream, &compile_error) catch |err| switch (err) {
        error.ParseError => |m| {
            try compile_error.render(std.io.getStdErr(), "");
            unreachable;
        },
        else => unreachable,
    };
}
