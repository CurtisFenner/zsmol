// ir.zig
// Defines the intermediate representation of Smol programs that can be compiled
// to a target or interpreted directly.

pub const Name = []const u8;

pub const VarID = struct {
    id: u32,
};

pub const RecordID = struct {
    id: u32,
};

pub const Type = union(enum) {
    I64: void,
    Record: RecordID,
    GenericType: void,
};

pub const FunctionID = struct {
    id: u32,
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
        destinations: []const VarID,
        function: FunctionID,
        arguments: []const VarID,
    };
    StaticCall: StaticCall,

    pub const NewRecord = struct {
        destination: VarID,
        record_type: RecordID,
        fields: []const VarID,
    };
    NewRecord: NewRecord,

    pub const ConstantI64 = struct {
        destination: VarID,
        value: i64,
    };
    ConstantI64: ConstantI64,

    pub const RecordField = struct {
        destination: VarID,
        record: VarID,
        field: usize,
    };
    RecordField: RecordField,
};

pub const Function = struct {
    name: Name,
    argument_types: []const Type,
    argument_names: []const Name,
    return_types: []const Type,
    return_names: []const Name,
    body: []const Op,
};

pub const Record = struct {
    name: Name,
    field_types: []const Type,
    field_names: []const Name,
};

pub const Program = struct {
    functions: []const Function,
    records: []const Record,
};
