// interpreter.zig
// An interpreter for the Smol IR.

const std = @import("std");
const assert = std.debug.assert;

const ir = @import("./ir.zig");

pub const Value = union(enum) {
    pub const Record = struct {
        typ: ir.Type,
        fields: []Value,
    };
    Record: Record,
    Boolean: bool,
    I64: i64,
};

const Point = struct {
    block: []const ir.Op,
    index: usize,
};

const Frame = struct {
    /// OWNED. The sequence of IDs in the parent frame that returns should write to.
    return_destinations: []const ir.VarID,

    /// OWNED.
    locals: []Value,

    counter_next: usize,

    /// OWNED.
    counters: []Point,

    fn init(interpreter: *Interpreter, return_destinations: []const ir.VarID, meta: FunctionMeta) !Frame {
        var locals = try interpreter._allocator.alloc(Value, meta.num_locals);
        errdefer interpreter._allocator.free(locals);

        var points = try interpreter._allocator.alloc(Point, meta.num_depth);
        errdefer interpreter._allocator.free(points);
        points[0] = Point{
            .block = interpreter.program.functions[meta.id.id].body,
            .index = 0,
        };
        return Frame{
            .return_destinations = return_destinations,
            .locals = locals,
            .counters = points,
            .counter_next = 1,
        };
    }

    fn deinit(frame: Frame, interpreter: *Interpreter) void {
        interpreter._allocator.free(frame.counters);
        interpreter._allocator.free(frame.locals);
    }
};

fn opsDepth(ops: []const ir.Op) usize {
    var max: usize = 1;
    for (ops) |op| {
        max = std.math.max(max, opDepth(op));
    }
    return max;
}

fn opDepth(op: ir.Op) usize {
    switch (op) {
        .Assign => return 1,
        .IfElse => |ie| {
            return 1 + std.math.max(opsDepth(ie.then_block), opsDepth(ie.else_block));
        },
        .Return => return 1,
        .NewRecord => return 1,
        .StaticCall => return 1,
        .ConstantI64 => return 1,
        .RecordField => return 1,
    }
}

fn opsMaxLocal(ops: []const ir.Op) usize {
    var out: usize = 0;
    for (ops) |op| {
        out = std.math.max(out, opMaxLocal(op));
    }
    return out;
}

fn opMaxLocal(op: ir.Op) usize {
    switch (op) {
        .Assign => |a| return std.math.max(a.destination.id, a.source.id),
        .IfElse => |ie| {
            return std.math.max(opsMaxLocal(ie.then_block), opsMaxLocal(ie.else_block));
        },
        .Return => |r| {
            var out: usize = 0;
            for (r.vars) |v| {
                out = std.math.max(out, v.id);
            }
            return out;
        },
        .StaticCall => |sc| {
            var out: usize = 0;
            for (sc.destinations) |v| {
                out = std.math.max(out, v.id);
            }
            for (sc.arguments) |v| {
                out = std.math.max(out, v.id);
            }
            return out;
        },
        .NewRecord => |nr| {
            var out = nr.destination.id;
            for (nr.fields) |v| {
                out = std.math.max(out, v.id);
            }
            return out;
        },
        .ConstantI64 => return 0,
        .RecordField => |rf| {
            return std.math.max(rf.destination.id, rf.record.id);
        },
    }
}

const FunctionMeta = struct {
    id: ir.FunctionID,
    num_locals: usize,
    num_depth: usize,

    fn measure(f: ir.Function, i: u32) FunctionMeta {
        return FunctionMeta{
            .id = ir.FunctionID{ .id = i },
            .num_locals = 1 + std.math.max(f.argument_types.len, opsMaxLocal(f.body)),
            .num_depth = opsDepth(f.body),
        };
    }
};

pub const Interpreter = struct {
    program: ir.Program,
    _allocator: *std.mem.Allocator,
    _function_metas: []const FunctionMeta,
    _stack: std.ArrayList(Frame),
    _result: []Value,

    pub const Invocation = struct {
        main: ir.FunctionID,
        arguments: []const Value,
    };

    /// RETURNS an interpreter for the given program.
    pub fn init(allocator: *std.mem.Allocator, program: ir.Program, invocation: Invocation) !Interpreter {
        var function_metas = try allocator.alloc(FunctionMeta, program.functions.len);
        errdefer allocator.free(function_metas);
        for (program.functions) |f, i| {
            function_metas[i] = FunctionMeta.measure(f, @intCast(u32, i));
        }

        const main = program.functions[invocation.main.id];
        var stack = std.ArrayList(Frame).init(allocator);

        var result = try allocator.alloc(Value, main.return_types.len);
        errdefer allocator.free(result);

        var interpreter = Interpreter{
            .program = program,
            ._allocator = allocator,
            ._result = result,
            ._function_metas = function_metas,
            ._stack = stack,
        };

        const root_meta = function_metas[invocation.main.id];
        var root_frame = try Frame.init(&interpreter, [_]ir.VarID{}, root_meta);
        errdefer root_frame.deinit(&interpreter);

        assert(invocation.arguments.len == main.argument_types.len);
        for (invocation.arguments) |a, i| {
            root_frame.locals[i] = a;
        }

        try interpreter._stack.append(root_frame);

        return interpreter;
    }

    fn workOp(interpreter: *Interpreter) !usize {
        const frame_count = interpreter._stack.items.len;
        assert(frame_count != 0);

        const frame = &interpreter._stack.toSlice()[frame_count - 1];
        const counter = frame.counters[frame.counter_next - 1];
        const op = counter.block[counter.index];

        // Advance to the next instruction.
        if (counter.index + 1 < counter.block.len) {
            frame.counters[frame.counter_next - 1] = Point{
                .block = counter.block,
                .index = counter.index + 1,
            };
        } else {
            frame.counter_next -= 1;
        }

        // Execute the instruction.
        switch (op) {
            .Assign => |a| {
                frame.locals[a.destination.id] = frame.locals[a.source.id];
                return 1;
            },
            .IfElse => |ie| {
                switch (frame.locals[ie.condition.id]) {
                    .Boolean => |condition| {
                        if (condition) {
                            if (ie.then_block.len != 0) {
                                frame.counters[frame.counter_next] = Point{
                                    .block = ie.then_block,
                                    .index = 0,
                                };
                                frame.counter_next += 1;
                            }
                        } else {
                            if (ie.else_block.len != 0) {
                                frame.counters[frame.counter_next] = Point{
                                    .block = ie.else_block,
                                    .index = 0,
                                };
                                frame.counter_next += 1;
                            }
                        }
                        return 2;
                    },
                    else => unreachable,
                }
            },
            .Return => |r| {
                if (frame_count == 1) {
                    // Return into the `values` slices.
                    assert(r.vars.len == interpreter._result.len);
                    for (r.vars) |v, i| {
                        interpreter._result[i] = frame.locals[v.id];
                    }
                } else {
                    // Return into the parent frame.
                    const parent_frame = &interpreter._stack.toSlice()[frame_count - 1];
                    assert(r.vars.len == frame.return_destinations.len);
                    for (r.vars) |v, i| {
                        parent_frame.locals[frame.return_destinations[i].id] = frame.locals[v.id];
                    }
                }
                interpreter._allocator.free(frame.locals);
                interpreter._allocator.free(frame.counters);
                _ = interpreter._stack.pop();
                return 1 + r.vars.len;
            },
            .StaticCall => |sc| {
                const function = interpreter.program.functions[sc.function.id];
                assert(sc.arguments.len == function.argument_types.len);
                assert(sc.destinations.len == function.return_types.len);

                const meta = interpreter._function_metas[sc.function.id];
                var callee = try Frame.init(interpreter, sc.destinations, meta);
                errdefer callee.deinit(interpreter);
                for (sc.arguments) |v, i| {
                    callee.locals[i] = frame.locals[v.id];
                }
                try interpreter._stack.append(callee);
                return 1 + sc.destinations.len + sc.arguments.len;
            },
            .NewRecord => |nr| {
                var fields = try interpreter._allocator.alloc(Value, nr.fields.len);
                for (nr.fields) |v, i| {
                    fields[i] = frame.locals[i];
                }
                frame.locals[nr.destination.id] = Value{
                    .Record = Value.Record{ .typ = ir.Type{ .Record = nr.record_type }, .fields = fields },
                };
                return 1 + nr.fields.len;
            },
            .ConstantI64 => |c| {
                frame.locals[c.destination.id] = Value{ .I64 = c.value };
                return 1;
            },
            .RecordField => |rf| {
                frame.locals[rf.destination.id] = frame.locals[rf.record.id].Record.fields[rf.field];
                return 1;
            },
        }
    }

    /// RETURNS the result of main when main has finished.
    /// RETURNS `null` when main has not finished.
    /// `steps` controls the amount of work done. Execution time is
    /// approximately proportional to `steps`.
    pub fn work(interpreter: *Interpreter, steps: usize) !?[]Value {
        var remaining = steps;
        while (true) {
            if (interpreter._stack.len == 0) {
                return interpreter._result;
            }

            const step = try interpreter.workOp();
            if (remaining < step) {
                return null;
            }
            remaining -= step;
        }
    }
};

test "Interpret identity program" {
    const program = ir.Program{
        .functions = [_]ir.Function{ir.Function{
            .name = "foo",
            .argument_types = [_]ir.Type{ir.Type{ .I64 = {} }},
            .argument_names = [_]ir.Name{""},
            .return_types = [_]ir.Type{ir.Type{ .I64 = {} }},
            .return_names = [_]ir.Name{""},
            .body = [_]ir.Op{ir.Op{
                .Return = ir.Op.Return{ .vars = [_]ir.VarID{ir.VarID{ .id = 0 }} },
            }},
        }},
        .records = [_]ir.Record{},
    };

    const invocation = Interpreter.Invocation{
        .main = ir.FunctionID{ .id = 0 },
        .arguments = [_]Value{Value{ .I64 = 1337 }},
    };
    var ip = try Interpreter.init(std.testing.allocator, program, invocation);
    var result = (try ip.work(1024)) orelse unreachable;
    assert(result.len == 1);
    assert(result[0].I64 == 1337);
}

test "Interpret `return 1234`" {
    const program = ir.Program{
        .functions = [_]ir.Function{ir.Function{
            .name = "foo",
            .argument_types = [_]ir.Type{},
            .argument_names = [_]ir.Name{},
            .return_types = [_]ir.Type{ir.Type{ .I64 = {} }},
            .return_names = [_]ir.Name{""},
            .body = [_]ir.Op{
                ir.Op{
                    .ConstantI64 = ir.Op.ConstantI64{ .destination = ir.VarID{ .id = 0 }, .value = 1234 },
                },
                ir.Op{
                    .Return = ir.Op.Return{ .vars = [_]ir.VarID{ir.VarID{ .id = 0 }} },
                },
            },
        }},
        .records = [_]ir.Record{},
    };

    const invocation = Interpreter.Invocation{
        .main = ir.FunctionID{ .id = 0 },
        .arguments = [_]Value{},
    };
    var ip = try Interpreter.init(std.testing.allocator, program, invocation);
    var result = (try ip.work(1024)) orelse unreachable;
    assert(result.len == 1);
    assert(result[0].I64 == 1234);
}

test "Interpret `if(arg){x=111}else{x=222}; return x;`" {
    const program = ir.Program{
        .functions = [_]ir.Function{ir.Function{
            .name = "foo",
            .argument_types = [_]ir.Type{ir.Type{ .I64 = {} }},
            .argument_names = [_]ir.Name{""},
            .return_types = [_]ir.Type{ir.Type{ .I64 = {} }},
            .return_names = [_]ir.Name{""},
            .body = [_]ir.Op{
                ir.Op{
                    .IfElse = ir.Op.IfElse{
                        .condition = ir.VarID{ .id = 0 },
                        .then_block = [_]ir.Op{ir.Op{
                            .ConstantI64 = ir.Op.ConstantI64{
                                .destination = ir.VarID{ .id = 1 },
                                .value = 111,
                            },
                        }},
                        .else_block = [_]ir.Op{ir.Op{
                            .ConstantI64 = ir.Op.ConstantI64{
                                .destination = ir.VarID{ .id = 1 },
                                .value = 222,
                            },
                        }},
                    },
                },
                ir.Op{
                    .Return = ir.Op.Return{ .vars = [_]ir.VarID{ir.VarID{ .id = 1 }} },
                },
            },
        }},
        .records = [_]ir.Record{},
    };

    const invocationFalse = Interpreter.Invocation{
        .main = ir.FunctionID{ .id = 0 },
        .arguments = [_]Value{Value{ .Boolean = false }},
    };
    var ipFalse = try Interpreter.init(std.testing.allocator, program, invocationFalse);
    var resultFalse = (try ipFalse.work(1024)) orelse unreachable;
    assert(resultFalse.len == 1);
    assert(resultFalse[0].I64 == 222);

    const invocationTrue = Interpreter.Invocation{
        .main = ir.FunctionID{ .id = 0 },
        .arguments = [_]Value{Value{ .Boolean = true }},
    };
    var ipTrue = try Interpreter.init(std.testing.allocator, program, invocationTrue);
    var resultTrue = (try ipTrue.work(1024)) orelse unreachable;
    assert(resultTrue.len == 1);
    assert(resultTrue[0].I64 == 111);
}

test "Interpret `if(arg){return 111}else{return 222}`" {
    const program = ir.Program{
        .functions = [_]ir.Function{ir.Function{
            .name = "f",
            .argument_types = [_]ir.Type{ir.Type{ .I64 = {} }},
            .argument_names = [_]ir.Name{""},
            .return_types = [_]ir.Type{ir.Type{ .I64 = {} }},
            .return_names = [_]ir.Name{""},
            .body = [_]ir.Op{ir.Op{
                .IfElse = ir.Op.IfElse{
                    .condition = ir.VarID{ .id = 0 },
                    .then_block = [_]ir.Op{
                        ir.Op{
                            .ConstantI64 = ir.Op.ConstantI64{
                                .destination = ir.VarID{ .id = 1 },
                                .value = 111,
                            },
                        },
                        ir.Op{
                            .Return = ir.Op.Return{ .vars = [_]ir.VarID{ir.VarID{ .id = 1 }} },
                        },
                    },
                    .else_block = [_]ir.Op{
                        ir.Op{
                            .ConstantI64 = ir.Op.ConstantI64{
                                .destination = ir.VarID{ .id = 1 },
                                .value = 222,
                            },
                        },
                        ir.Op{
                            .Return = ir.Op.Return{ .vars = [_]ir.VarID{ir.VarID{ .id = 1 }} },
                        },
                    },
                },
            }},
        }},
        .records = [_]ir.Record{},
    };

    const invocationFalse = Interpreter.Invocation{
        .main = ir.FunctionID{ .id = 0 },
        .arguments = [_]Value{Value{ .Boolean = false }},
    };
    var ipFalse = try Interpreter.init(std.testing.allocator, program, invocationFalse);
    var resultFalse = (try ipFalse.work(1024)) orelse unreachable;
    assert(resultFalse.len == 1);
    assert(resultFalse[0].I64 == 222);

    const invocationTrue = Interpreter.Invocation{
        .main = ir.FunctionID{ .id = 0 },
        .arguments = [_]Value{Value{ .Boolean = true }},
    };
    var ipTrue = try Interpreter.init(std.testing.allocator, program, invocationTrue);
    var resultTrue = (try ipTrue.work(1024)) orelse unreachable;
    assert(resultTrue.len == 1);
    assert(resultTrue[0].I64 == 111);
}

test "Interpret `if(arg){}else{}return 333;`" {
    const program = ir.Program{
        .functions = [_]ir.Function{ir.Function{
            .name = "f",
            .argument_types = [_]ir.Type{ir.Type{ .I64 = {} }},
            .argument_names = [_]ir.Name{""},
            .return_types = [_]ir.Type{ir.Type{ .I64 = {} }},
            .return_names = [_]ir.Name{""},
            .body = [_]ir.Op{
                ir.Op{
                    .IfElse = ir.Op.IfElse{
                        .condition = ir.VarID{ .id = 0 },
                        .then_block = [_]ir.Op{},
                        .else_block = [_]ir.Op{},
                    },
                },
                ir.Op{
                    .ConstantI64 = ir.Op.ConstantI64{
                        .destination = ir.VarID{ .id = 1 },
                        .value = 333,
                    },
                },
                ir.Op{
                    .Return = ir.Op.Return{
                        .vars = [_]ir.VarID{ir.VarID{ .id = 1 }},
                    },
                },
            },
        }},
        .records = [_]ir.Record{},
    };

    const invocationFalse = Interpreter.Invocation{
        .main = ir.FunctionID{ .id = 0 },
        .arguments = [_]Value{Value{ .Boolean = false }},
    };
    var ipFalse = try Interpreter.init(std.testing.allocator, program, invocationFalse);
    var resultFalse = (try ipFalse.work(1024)) orelse unreachable;
    assert(resultFalse.len == 1);
    assert(resultFalse[0].I64 == 333);

    const invocationTrue = Interpreter.Invocation{
        .main = ir.FunctionID{ .id = 0 },
        .arguments = [_]Value{Value{ .Boolean = true }},
    };
    var ipTrue = try Interpreter.init(std.testing.allocator, program, invocationTrue);
    var resultTrue = (try ipTrue.work(1024)) orelse unreachable;
    assert(resultTrue.len == 1);
    assert(resultTrue[0].I64 == 333);
}

test "Interpret `r=new(11,22,33); return r.0,r.1,r.2`" {
    const program = ir.Program{
        .functions = [_]ir.Function{ir.Function{
            .name = "f",
            .argument_types = [_]ir.Type{},
            .argument_names = [_]ir.Name{},
            .return_types = [_]ir.Type{ir.Type{ .I64 = {} }} ** 3,
            .return_names = [_]ir.Name{""} ** 3,
            .body = [_]ir.Op{
                ir.Op{ .ConstantI64 = ir.Op.ConstantI64{ .destination = ir.VarID{ .id = 0 }, .value = 11 } },
                ir.Op{ .ConstantI64 = ir.Op.ConstantI64{ .destination = ir.VarID{ .id = 1 }, .value = 22 } },
                ir.Op{ .ConstantI64 = ir.Op.ConstantI64{ .destination = ir.VarID{ .id = 2 }, .value = 33 } },
                ir.Op{
                    .NewRecord = ir.Op.NewRecord{
                        .destination = ir.VarID{ .id = 3 },
                        .record_type = ir.RecordID{ .id = 0 },
                        .fields = [_]ir.VarID{ ir.VarID{ .id = 0 }, ir.VarID{ .id = 1 }, ir.VarID{ .id = 2 } },
                    },
                },
                ir.Op{
                    .RecordField = ir.Op.RecordField{
                        .destination = ir.VarID{ .id = 4 },
                        .record = ir.VarID{ .id = 3 },
                        .field = 0,
                    },
                },
                ir.Op{
                    .RecordField = ir.Op.RecordField{
                        .destination = ir.VarID{ .id = 5 },
                        .record = ir.VarID{ .id = 3 },
                        .field = 1,
                    },
                },
                ir.Op{
                    .RecordField = ir.Op.RecordField{
                        .destination = ir.VarID{ .id = 6 },
                        .record = ir.VarID{ .id = 3 },
                        .field = 2,
                    },
                },
                ir.Op{
                    .Return = ir.Op.Return{ .vars = [_]ir.VarID{ ir.VarID{ .id = 4 }, ir.VarID{ .id = 5 }, ir.VarID{ .id = 6 } } },
                },
            },
        }},
        .records = [_]ir.Record{ir.Record{
            .name = "r",
            .field_types = [_]ir.Type{ir.Type{ .I64 = {} }} ** 3,
            .field_names = [_]ir.Name{""},
        }},
    };

    const invocation = Interpreter.Invocation{
        .main = ir.FunctionID{ .id = 0 },
        .arguments = [_]Value{},
    };
    var ip = try Interpreter.init(std.testing.allocator, program, invocation);
    var result = (try ip.work(1024)) orelse unreachable;
    assert(result.len == 3);
    assert(result[0].I64 == 11);
    assert(result[1].I64 == 22);
    assert(result[2].I64 == 33);
}
