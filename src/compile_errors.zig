const Identifier = @import("identifiers.zig").Identifier;
const parser = @import("parser.zig");
const Location = parser.Location;
const ErrorMessage = parser.ErrorMessage;

pub const ImportUnknownObjectErr = struct {
    object_iden: Identifier,
    package_iden: Identifier,
    import_location: Location,

    pub fn err(error_message: *ErrorMessage, self: @This()) error{CompileError} {
        error_message.* = ErrorMessage.make(&[_]ErrorMessage.Entry{
            .{ .Text = "There is no object named `" },
            .{ .Text = self.object_iden.string() },
            .{ .Text = "` in package `" },
            .{ .Text = self.package_iden.string() },
            .{ .Text = "` but an import is attempted" },
            .{ .AtLocation = self.import_location },
        });
        return error.CompileError;
    }
};

pub const ObjectRedefinedErr = struct {
    package_iden: Identifier,
    object_iden: Identifier,
    first_definition_location: Location,
    second_definition_location: Location,

    pub fn err(error_message: *ErrorMessage, self: @This()) error{CompileError} {
        error_message.* = ErrorMessage.make(&[_]ErrorMessage.Entry{
            .{ .Text = "The object `" },
            .{ .Text = self.package_iden.string() },
            .{ .Text = ":" },
            .{ .Text = self.object_iden.string() },
            .{ .Text = "` is defined for a second time in the `" },
            .{ .Text = self.package_iden.string() },
            .{ .Text = "` package" },
            .{ .AtLocation = self.second_definition_location },
            .{ .Text = "The first definition was" },
            .{ .AtLocation = self.first_definition_location },
        });
        return error.CompileError;
    }
};

pub const ObjectReimportedErr = struct {
    object_iden: Identifier,
    first_binding_location: Location,
    import_location: Location,

    pub fn err(error_message: *ErrorMessage, self: @This()) error{CompileError} {
        error_message.* = ErrorMessage.make(&[_]ErrorMessage.Entry{
            .{ .Text = "The name `" },
            .{ .Text = self.object_iden.string() },
            .{ .Text = "` had already been bound" },
            .{ .AtLocation = self.first_binding_location },
            .{ .Text = "However, it was imported again" },
            .{ .AtLocation = self.import_location },
        });
        return error.CompileError;
    }
};

pub const PackageReimportedErr = struct {
    package_iden: Identifier,
    first_binding_location: Location,
    import_location: Location,

    pub fn err(error_message: *ErrorMessage, self: @This()) error{CompileError} {
        error_message.* = ErrorMessage.make(&[_]ErrorMessage.Entry{
            .{ .Text = "The package `" },
            .{ .Text = self.package_iden.string() },
            .{ .Text = "` had already been bound" },
            .{ .AtLocation = self.first_binding_location },
            .{ .Text = "However, it was imported again" },
            .{ .AtLocation = self.import_location },
        });
        return error.CompileError;
    }
};

pub const UnknownPackageReferencedErr = struct {
    package_iden: Identifier,
    reference_location: Location,

    pub fn err(error_message: *ErrorMessage, self: @This()) error{CompileError} {
        error_message.* = ErrorMessage.make(&[_]ErrorMessage.Entry{
            .{ .Text = "There is no package named `" },
            .{ .Text = self.package_iden.string() },
            .{ .Text = "`, but it was referenced" },
            .{ .AtLocation = self.reference_location },
        });
        return error.CompileError;
    }
};

pub const PackageImportSelfErr = struct {
    package_name: Identifier,
    import_location: Location,

    pub fn err(error_message: *ErrorMessage, self: @This()) error{CompileError} {
        error_message.* = ErrorMessage.make(&[_]ErrorMessage.Entry{
            .{ .Text = "A package cannot import itself.\n" },
            .{ .Text = "However, the package `" },
            .{ .Text = self.package_name.string() },
            .{ .Text = "` attempts to import itself" },
            .{ .AtLocation = self.import_location },
        });
        return error.CompileError;
    }
};

pub const InterfaceConstraintUsedAsTypeArgument = struct {
    package_name: Identifier,
    object_name: Identifier,
    argument_location: Location,

    pub fn err(error_message: *ErrorMessage, self: @This()) error{CompileError} {
        error_message.* = ErrorMessage.make(&[_]ErrorMessage.Entry{
            .{ .Text = "The interface constraint `" },
            .{ .Text = self.package_name.string() },
            .{ .Text = ":" },
            .{ .Text = self.object_name.string() },
            .{ .Text = "` is not a type, and cannot be used as a type argument like" },
            .{ .AtLocation = self.argument_location },
        });
        return error.CompileError;
    }
};

pub const ImplementsNonConstraintErr = struct {
    claim_location: Location,

    pub fn err(error_message: *ErrorMessage, self: @This()) error{CompileError} {
        error_message.* = ErrorMessage.make(&[_]ErrorMessage.Entry{
            .{ .Text = "Only constraints can be implemented.\n" },
            .{ .Text = "However, a type is used" },
            .{ .AtLocation = self.claim_location },
        });
        return error.CompileError;
    }
};

pub const UnknownUnqualifiedObjectReferencedErr = struct {
    object_name: Identifier,
    reference_location: Location,

    pub fn err(error_message: *ErrorMessage, self: @This()) error{CompileError} {
        error_message.* = ErrorMessage.make(&[_]ErrorMessage.Entry{
            .{ .Text = "There is no object named `" },
            .{ .Text = self.object_name.string() },
            .{ .Text = "` but it is referenced" },
            .{ .AtLocation = self.reference_location },
        });
        return error.CompileError;
    }
};

pub const TypeParameterRedefinedErr = struct {
    type_parameter_name: Identifier,
    first_binding_location: Location,
    second_binding_location: Location,

    pub fn err(error_message: *ErrorMessage, self: @This()) error{CompileError} {
        error_message.* = ErrorMessage.make(&[_]ErrorMessage.Entry{
            .{ .Text = "The type parameter `#" },
            .{ .Text = self.type_parameter_name.string() },
            .{ .Text = "` is defined for a second time" },
            .{ .AtLocation = self.second_binding_location },
            .{ .Text = "The first definition was" },
            .{ .AtLocation = self.first_binding_location },
        });
        return error.CompileError;
    }
};
