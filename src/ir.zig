// ir.zig
// Defines the intermediate representation of Smol programs that can be compiled
// to a target or interpreted directly.

pub const IR = struct {
    arena: std.heap.ArenaAllocator,

    fn init(allocator: *std.mem.Allocator) IR {
        return IR{
            .arena = std.heap.ArenaAllocator.init(allocator),
        };
    }
};

pub const RecordType = struct {
    record_id: u32,
    arguments: []const Type,
};

pub const Type = union(enum) {
    I64: void,
    Record: RecordType,
    GenericType: u32,
};

pub const FunctionSignature = struct {
    type_argument_count: u32,
    return_types: []const Type,
    arguments: []const Type,
    vtable_arguments: []const VTableInstantiation,
};

pub const VTableSignature = struct {
    id: u32,
    type_argument_count: u32,
    signatures: []const FunctionSignature,
};

pub const VTableInstantiation = struct {
    id: u32,
    arguments: []const Type,
};

pub const Function = struct {
    signature: FunctionSignature,
};

pub const Op = union(enum) {
    pub const Assign = struct {
        destination: VarID,
        source: VarID,
    };
    Assign: Assign,

    pub const IfElse = struct {
        condition: VarID,
        then_block: []const Op,
        else_block: []const Op,
    };
    IfElse: IfElse,

    pub const Return = struct {
        vars: []const VarID,
    };
    Return: Return,

    /// Variables [0, arguments.length) in the callee's stack will be initialized
    /// with the given arguments.
    pub const StaticCall = struct {
        function: u32,
        destination_vars: []const u32,
        type_arguments: []const Type,
        vtable_arguments: []const VTableArgument,
        argument_vars: []const u32,
    };
    StaticCall: StaticCall,

    pub const NewRecord = struct {
        destination_var: u32,
        record_id: u32,
        field_vars: []const u32,
    };
    NewRecord: NewRecord,

    pub const ConstantI64 = struct {
        destination_var: u32,
        value: i64,
    };
    ConstantI64: ConstantI64,

    pub const RecordField = struct {
        destination_var: u32,
        record_var: u32,
        field_index: u32,
    };
    RecordField: RecordField,
};

pub const Record = struct {
    type_argument_count: u32,
    field_types: []const Type,
};

pub const Program = struct {
    functions: []const Function,
    records: []const Record,
    vtable_signatures: []const VTableSignature,
};
