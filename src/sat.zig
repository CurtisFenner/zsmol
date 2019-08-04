const std = @import("std");
const assert = std.debug.assert;

pub fn log(comptime fmt: []const u8, args: ...) void {
    //  std.debug.warn(fmt, args);
}

pub const CNF = struct {
    const TermInfo = struct {
        /// Index of clauses satisfied by a `true` assignment.
        clauses_positive: std.ArrayList(usize),

        /// Index of clauses satisfied by a `false` assignment.
        clauses_negative: std.ArrayList(usize),

        fn init(allocator: *std.mem.Allocator) TermInfo {
            return TermInfo{
                .clauses_positive = std.ArrayList(usize).init(allocator),
                .clauses_negative = std.ArrayList(usize).init(allocator),
            };
        }

        fn deinit(self: *const TermInfo) void {
            self.clauses_positive.deinit();
            self.clauses_negative.deinit();
        }

        fn clausesNeeding(term_info: TermInfo, assignment: bool) []const usize {
            if (assignment) {
                return term_info.clauses_positive.toSlice();
            }
            return term_info.clauses_negative.toSlice();
        }
    };

    const Assignment = struct {
        term: usize,
        assignment: bool,

        /// clause_index is null for "free" choices.
        /// clause_index is the clause that forced a unit assignment otherwise.
        cause_clause_index: ?usize,

        /// decision_level is the number of free decision that have been made.
        /// Initial unit-prop and pure-literals are assigned decision level 0.
        decision_level: usize,
    };

    allocator: *std.mem.Allocator,
    clauses: std.ArrayList(Clause),
    term_info: std.ArrayList(TermInfo),
    conflict: std.ArrayList(usize),
    diagnose_tmp: std.ArrayList(usize),

    /// Creates an empty clause database (with no terms and no clauses).
    pub fn init(allocator: *std.mem.Allocator) CNF {
        return CNF{
            .allocator = allocator,
            .clauses = std.ArrayList(Clause).init(allocator),
            .term_info = std.ArrayList(TermInfo).init(allocator),
            .conflict = std.ArrayList(usize).init(allocator),
            .diagnose_tmp = std.ArrayList(usize).init(allocator),
        };
    }

    pub fn deinit(self: *CNF) void {
        for (self.clauses.toSlice()) |clause| {
            self.allocator.free(clause.literals);
        }
        self.clauses.deinit();
        for (self.term_info.toSlice()) |info| {
            info.deinit();
        }
        self.term_info.deinit();
        self.conflict.deinit();
        self.diagnose_tmp.deinit();
    }

    fn diagnoseConflict(self: *CNF, assignment: []const ?Assignment, conflicting: Assignment) !void {
        self.conflict.shrink(0);

        // The arguments implicitly represent the "implication graph",
        // which is a DAG formed as follows:
        // The literals in the assignment are vertices.
        // (Only the `conflict` literal appears both positively and negatively)
        // For every Assignment with a cause_clause_index,
        // a "parent" edge is added from the assigned literal to all of the other
        // literals in the clause.

        // Thus, "freely" chosen terms are roots. Our goal is to find a small
        // clause that's backed up a bit along the graph.

        // TODO: Implement a real conflict analysis like rel-sat; instead
        // just use all of the roots.

        // TODO: Reuse this memory.
        var seen = try self.allocator.alloc(bool, assignment.len);
        defer self.allocator.free(seen);
        for (seen) |*v| {
            v.* = false;
        }

        self.diagnose_tmp.shrink(0);
        try self.diagnose_tmp.append(conflicting.cause_clause_index.?);
        try self.diagnose_tmp.append(assignment[conflicting.term].?.cause_clause_index.?);
        seen[conflicting.term] = true;
        while (self.diagnose_tmp.count() != 0) {
            var top_clause = self.clauses.at(self.diagnose_tmp.pop());
            for (top_clause.literals) |literal| {
                if (!seen[literal.term]) {
                    seen[literal.term] = true;
                    assert(assignment[literal.term] != null);
                    if (assignment[literal.term].?.cause_clause_index) |cause_clause_index| {
                        try self.diagnose_tmp.append(cause_clause_index);
                    } else {
                        try self.conflict.append(literal.term);
                    }
                }
            }
        }

        var all: usize = 0;
        for (assignment) |a| {
            if (a) |assigned| {
                if (assigned.cause_clause_index == null) {
                    // try self.conflict.append(assigned.term);
                    all += 1;
                }
            }
        }
    }

    /// RETURNS null when this CNF is not satisfiable.
    /// RETURNS a boolean satisfiaction when this CNF is satisfiable.
    /// The returned slice must be freed by the caller.
    pub fn satisfiable(self: *CNF) !?[]const bool {
        log("\n====\n");
        defer log("<<<<\n\n");

        var assignment = try self.allocator.alloc(?Assignment, self.term_info.count());
        defer self.allocator.free(assignment);
        for (assignment) |_, i| {
            assignment[i] = null;
        }

        // Preprocess the input:
        // Find unit clauses and pure literals.
        var unit_literals = std.ArrayList(Assignment).init(self.allocator);
        defer unit_literals.deinit();
        const SignCounts = struct {
            positive: usize,
            negative: usize,
        };
        var sign_counts_list = std.ArrayList(SignCounts).init(self.allocator);
        defer sign_counts_list.deinit();
        while (true) {
            // Reset the statistics.
            var unsatisfied_clause_count: usize = 0;
            sign_counts_list.shrink(0);
            for (assignment) |term| {
                try sign_counts_list.append(SignCounts{ .positive = 0, .negative = 0 });
            }
            var sign_counts = sign_counts_list.toSlice();
            unit_literals.shrink(0);

            // Find all unit clauses and count occurrences for pure literals.
            for (self.clauses.toSlice()) |clause, clause_index| {
                var satisfied = false;
                var unknown_count: usize = 0;
                var last_unknown: ?Assignment = null;
                for (clause.literals) |literal| {
                    if (assignment[literal.term]) |assigned| {
                        if (assigned.assignment == literal.sign) {
                            satisfied = true;
                        }
                    } else {
                        unknown_count += 1;
                        last_unknown = Assignment{
                            .term = literal.term,
                            .assignment = literal.sign,
                            .cause_clause_index = clause_index,
                            .decision_level = 0,
                        };
                    }
                }

                if (!satisfied) {
                    unsatisfied_clause_count += 1;
                }
                if (!satisfied and unknown_count == 1) {
                    try unit_literals.append(last_unknown.?);
                }
                if (!satisfied) {
                    for (clause.literals) |literal| {
                        if (assignment[literal.term] == null) {
                            if (literal.sign) {
                                sign_counts[literal.term].positive += 1;
                            } else {
                                sign_counts[literal.term].negative += 1;
                            }
                        }
                    }
                }
            }

            // Assign all unit clauses and pure literals.
            var progress_made = false;
            for (unit_literals.toSlice()) |unit_literal| {
                if (assignment[unit_literal.term]) |assigned| {
                    if (assigned.assignment != unit_literal.assignment) {
                        // A contradiction was hit.
                        return null;
                    }
                } else {
                    log("@ Initial unit: {}\n", unit_literal);
                    progress_made = true;
                    assignment[unit_literal.term] = unit_literal;
                }
            }
            for (sign_counts) |sign_count, term| {
                if (assignment[term] == null) {
                    // Identify and assign pure literals.
                    if (sign_count.positive == 0 or sign_count.negative == 0) {
                        if (sign_count.positive != 0) {
                            assignment[term] = Assignment{
                                .assignment = true,
                                .cause_clause_index = null,
                                .term = term,
                                .decision_level = 0,
                            };
                            progress_made = true;
                            log("@ Initial pure: {}\n", assignment[term]);
                        } else if (sign_count.negative != 0) {
                            assignment[term] = Assignment{
                                .assignment = false,
                                .cause_clause_index = null,
                                .term = term,
                                .decision_level = 0,
                            };
                            progress_made = true;
                            log("@ Initial pure: {}\n", assignment[term]);
                        }
                    }
                }
            }

            if (!progress_made) {
                break;
            }
        }

        // All initial pure literals and unit clauses have been removed.
        var decision_level: usize = 0;
        assert(unit_literals.count() == 0);
        var assigned_through: usize = 0;
        while (true) {
            var branch: Assignment = undefined;
            if (unit_literals.count() != 0) {
                // There is a forced assignment from a previous assignment.
                branch = unit_literals.pop();
            } else {
                // All are assigned.
                if (assigned_through == self.term_info.len) break;

                // Find an unassigned literal.
                if (assignment[assigned_through] != null) {
                    assigned_through += 1;
                    continue;
                }

                // Determine the sign to use. (For now, just true).
                decision_level += 1;
                const choice = true;
                branch = Assignment{
                    .cause_clause_index = null,
                    .assignment = choice,
                    .term = assigned_through,
                    .decision_level = decision_level,
                };
            }
            log("@ Choice: {} (through {})\n", branch, assigned_through);

            if (assignment[branch.term]) |previous| {
                assert(previous.assignment == branch.assignment);
                continue;
            } else {
                assignment[branch.term] = branch;
            }

            // Find any unit clauses that were created.
            const term_info = self.term_info.at(branch.term);
            var possible_unit_clauses = term_info.clausesNeeding(!branch.assignment);
            for (possible_unit_clauses) |clause_index| {
                const analysis = self.clauses.at(clause_index).analyze(assignment);
                if (!analysis.satisfied) {
                    if (analysis.undetermined[0] == null) {
                        log("@ Conflict!\n\n");
                        // This term was simultaneously a positive and negative unit literal.
                        // Diagnose a conflict and backtrack:
                        assert(branch.cause_clause_index != null);
                        try self.diagnoseConflict(assignment, Assignment{
                            .cause_clause_index = clause_index,
                            .assignment = !branch.assignment,
                            .term = branch.term,
                            .decision_level = decision_level,
                        });

                        // Add the conflict clause:
                        var conflict_clause = try self.allocator.alloc(Literal, self.conflict.count());
                        errdefer self.allocator.free(conflict_clause);
                        var bad_decision: usize = decision_level;
                        for (self.conflict.toSlice()) |term, i| {
                            const assigned = assignment[term].?;
                            conflict_clause[i] = Literal{
                                .term = term,
                                .sign = !assigned.assignment,
                            };
                            if (bad_decision > assigned.decision_level) {
                                bad_decision = assigned.decision_level;
                            }
                            log("@ Problem set includes {}\n", assigned);
                        }
                        log("@ Bad decision level was {}\n", bad_decision);
                        if (bad_decision == 0 or self.conflict.count() == 0) {
                            log("@ Unsatisfiable.");
                            self.allocator.free(conflict_clause);
                            // A contradiction has been reached.
                            return null;
                        }

                        // Add the clause, then reset the decision level, assignment stack, and unit clause set.
                        try self.internalAddClause(conflict_clause);
                        decision_level = bad_decision - 1;

                        // Reset unit clauses to only possibly this one.
                        unit_literals.shrink(0);
                        if (conflict_clause.len == 1) {
                            try unit_literals.append(Assignment{
                                .term = conflict_clause[0].term,
                                .assignment = conflict_clause[0].sign,
                                .cause_clause_index = self.clauses.count() - 1,
                                .decision_level = decision_level,
                            });
                        }

                        for (assignment) |a, i| {
                            if (a) |assigned| {
                                if (assigned.decision_level >= bad_decision) {
                                    assignment[i] = null;
                                    if (i < assigned_through) {
                                        assigned_through = i;
                                    }
                                }
                            }
                        }
                        log("\n");
                        break;
                    } else if (analysis.undetermined[1] == null) {
                        // The clause is a unit clause.
                        var force = Assignment{
                            .term = analysis.undetermined[0].?.term,
                            .cause_clause_index = clause_index,
                            .assignment = analysis.undetermined[0].?.sign,
                            .decision_level = decision_level,
                        };
                        // TODO: Avoid adding duplicates.
                        try unit_literals.append(force);
                    }
                }
            }
        }

        // All terms are assigned.
        var out = try self.allocator.alloc(bool, assignment.len);
        for (assignment) |a, i| {
            out[i] = a.?.assignment;
        }
        return out;
    }

    pub const Clause = struct {
        const Analysis = struct {
            satisfied: bool,
            undetermined: [2]?Literal,
        };

        /// Analyzes this clause in the given assignment.
        /// Determines if this clause is satisfied, and otherwise produces up to
        /// to undetermined literals that remain.
        fn analyze(clause: Clause, assignment: []const ?Assignment) Analysis {
            var satisfied = false;
            var undetermined = [_]?Literal{ null, null };
            for (clause.literals) |literal| {
                if (assignment[literal.term]) |assigned| {
                    if (assigned.assignment == literal.sign) {
                        satisfied = true;
                    }
                } else {
                    if (undetermined[0] == null) {
                        undetermined[0] = literal;
                    } else {
                        undetermined[1] = literal;
                    }
                }
            }
            return Analysis{ .satisfied = satisfied, .undetermined = undetermined };
        }

        literals: []const Literal,
    };

    fn internalAddClause(self: *CNF, literals: []const Literal) !void {
        const clause_index = self.clauses.count();
        for (literals) |literal| {
            var term_info = &self.term_info.toSlice()[literal.term];
            if (literal.sign) {
                try term_info.clauses_positive.append(clause_index);
            } else {
                try term_info.clauses_negative.append(clause_index);
            }
        }

        try self.clauses.append(Clause{
            // TODO: Should we copy so that ownership is clearer?
            .literals = literals,
        });
        // std.debug.warn("% Number of clauses: {}\n", self.clauses.count());
    }

    /// Adds a clause to this CNF clause database.
    /// REQUIRES literals is not empty.
    pub fn addClause(self: *CNF, literals: []const Literal) !void {
        assert(literals.len != 0);

        // Grow the set of terms as needed.
        for (literals) |literal| {
            while (literal.term >= self.term_info.count()) {
                var term_info = TermInfo.init(self.allocator);
                try self.term_info.append(term_info);
            }
        }

        // TODO: Check for duplicates, and tautological clauses
        var copy = try self.allocator.alloc(Literal, literals.len);
        std.mem.copy(Literal, copy, literals);

        try self.internalAddClause(copy);
    }
};

pub const Literal = struct {
    // This literal is satisfied when the term is assigned the truth value of
    // `sign`. For example,
    // "x_0" is (0, true).
    // "~x_9" is (9, false).
    term: usize,
    sign: bool,
};

test "sat (x)" {
    var buffer: [10000]u8 = undefined;
    var allocator = &std.heap.FixedBufferAllocator.init(&buffer).allocator;
    var cnf = CNF.init(allocator);
    defer cnf.deinit();
    try cnf.addClause([_]Literal{Literal{ .term = 0, .sign = true }});

    const sat = (try cnf.satisfiable()).?;
    assert(sat.len == 1);
    assert(sat[0] == true);
}

test "unsat (x) and (~x)" {
    var buffer: [10000]u8 = undefined;
    var allocator = &std.heap.FixedBufferAllocator.init(&buffer).allocator;
    var cnf = CNF.init(allocator);
    defer cnf.deinit();
    try cnf.addClause([_]Literal{Literal{ .term = 0, .sign = true }});
    try cnf.addClause([_]Literal{Literal{ .term = 0, .sign = false }});

    const sat = try cnf.satisfiable();
    assert(sat == null);
}

test "sat (~x or y) and (x or ~y)" {
    var buffer: [10000]u8 = undefined;
    var allocator = &std.heap.FixedBufferAllocator.init(&buffer).allocator;
    var cnf = CNF.init(allocator);
    defer cnf.deinit();
    try cnf.addClause([_]Literal{ Literal{ .term = 1, .sign = false }, Literal{ .term = 0, .sign = true } });
    try cnf.addClause([_]Literal{ Literal{ .term = 1, .sign = true }, Literal{ .term = 0, .sign = false } });

    const sat = try cnf.satisfiable();
    assert(sat != null);
    assert(sat.?.len == 2);
    assert(sat.?[0] == sat.?[1]);
}

test "sat (x or y) and (~x or ~y)" {
    var buffer: [10000]u8 = undefined;
    var allocator = &std.heap.FixedBufferAllocator.init(&buffer).allocator;
    var cnf = CNF.init(allocator);
    defer cnf.deinit();
    try cnf.addClause([_]Literal{ Literal{ .term = 1, .sign = true }, Literal{ .term = 0, .sign = true } });
    try cnf.addClause([_]Literal{ Literal{ .term = 1, .sign = false }, Literal{ .term = 0, .sign = false } });

    const sat = try cnf.satisfiable();
    assert(sat != null);
    assert(sat.?.len == 2);
    assert(sat.?[0] != sat.?[1]);
}

const Testing = struct {
    const Range = struct {
        from: usize,
        limit: usize,
        fn next(r: *Range) ?usize {
            if (r.from >= r.limit) return null;
            var out = r.from;
            r.from += 1;
            return out;
        }
    };

    var literals: [100]Literal = [_]Literal{undefined} ** 100;

    fn literal(n: isize) Literal {
        assert(n != 0);
        if (n < 0) {
            return Literal{ .term = @intCast(usize, -n), .sign = false };
        }
        return Literal{ .term = @intCast(usize, n), .sign = true };
    }

    fn clause(lits: []const isize) []const Literal {
        for (lits) |lit, i| {
            literals[i] = Testing.literal(lit);
        }
        return literals[0..lits.len];
    }

    fn pigeon(cnf: *CNF, pigeons: usize, holes: usize) void {
        // Every pigeon is in one of the holes:
        var pr = Range{ .from = 0, .limit = pigeons };
        while (pr.next()) |p| {
            var hr = Range{ .from = 0, .limit = holes };
            while (hr.next()) |h| {
                literals[h] = Literal{ .term = p + h * pigeons, .sign = true };
            }
            cnf.addClause(literals[0..holes]) catch unreachable;
        }

        // Every hole holds only one pigeon:
        var hr = Range{ .from = 0, .limit = holes };
        while (hr.next()) |hole| {
            var pr_a = Range{ .from = 0, .limit = pigeons };
            while (pr_a.next()) |p_a| {
                var pr_b = Range{ .from = 0, .limit = p_a };
                while (pr_b.next()) |p_b| {
                    literals[0] = Literal{ .term = pigeons * hole + p_a, .sign = false };
                    literals[1] = Literal{ .term = pigeons * hole + p_b, .sign = false };
                    cnf.addClause(literals[0..2]) catch unreachable;
                }
            }
        }
    }
};

test "example" {
    var buffer: [100000]u8 = undefined;
    var allocator = &std.heap.FixedBufferAllocator.init(&buffer).allocator;
    var cnf = CNF.init(allocator);
    defer cnf.deinit();
    try cnf.addClause([_]Literal{Literal{ .term = 1, .sign = true }});

    try cnf.addClause(Testing.clause([_]isize{ 1, -9, -6 }));
    try cnf.addClause(Testing.clause([_]isize{ -8, 7, 4 }));
    try cnf.addClause(Testing.clause([_]isize{ -3, 1, 4 }));
    try cnf.addClause(Testing.clause([_]isize{ 1, -3, 6 }));
    try cnf.addClause(Testing.clause([_]isize{ 3, 4, -5 }));
    try cnf.addClause(Testing.clause([_]isize{ -9, 1, -7 }));
    try cnf.addClause(Testing.clause([_]isize{ -2, 6, 4 }));
    try cnf.addClause(Testing.clause([_]isize{ 2, -5, -8 }));
    try cnf.addClause(Testing.clause([_]isize{ 9, -8, -7 }));
    try cnf.addClause(Testing.clause([_]isize{ 9, 8, 4 }));
    try cnf.addClause(Testing.clause([_]isize{ 8, 5, 7 }));
    try cnf.addClause(Testing.clause([_]isize{ -1, 5, 2 }));
    try cnf.addClause(Testing.clause([_]isize{ -7, -6, 3 }));
    try cnf.addClause(Testing.clause([_]isize{ 1, 6, -4 }));
    try cnf.addClause(Testing.clause([_]isize{ -6, -4, 8 }));
    try cnf.addClause(Testing.clause([_]isize{ -7, -5, 2 }));
    try cnf.addClause(Testing.clause([_]isize{ -3, 4, 1 }));
    try cnf.addClause(Testing.clause([_]isize{ 2, -1, -9 }));
    try cnf.addClause(Testing.clause([_]isize{ -9, 4, -7 }));
    try cnf.addClause(Testing.clause([_]isize{ 2, 8, 9 }));
    try cnf.addClause(Testing.clause([_]isize{ 3, -9, -6 }));
    try cnf.addClause(Testing.clause([_]isize{ 9, -2, 7 }));
    try cnf.addClause(Testing.clause([_]isize{ -9, -8, -1 }));
    try cnf.addClause(Testing.clause([_]isize{ 4, -5, -8 }));
    try cnf.addClause(Testing.clause([_]isize{ 2, -5, -6 }));
    try cnf.addClause(Testing.clause([_]isize{ 7, -6, -9 }));
    try cnf.addClause(Testing.clause([_]isize{ 1, 7, 2 }));
    try cnf.addClause(Testing.clause([_]isize{ 2, -6, -1 }));
    try cnf.addClause(Testing.clause([_]isize{ -5, 4, 7 }));
    try cnf.addClause(Testing.clause([_]isize{ -2, -4, 9 }));
    try cnf.addClause(Testing.clause([_]isize{ 2, -1, -8 }));
    try cnf.addClause(Testing.clause([_]isize{ 4, -7, 8 }));
    try cnf.addClause(Testing.clause([_]isize{ -2, -8, 4 }));
    try cnf.addClause(Testing.clause([_]isize{ -5, 4, 3 }));
    try cnf.addClause(Testing.clause([_]isize{ 7, -8, 9 }));
    try cnf.addClause(Testing.clause([_]isize{ 4, 5, -8 }));
    try cnf.addClause(Testing.clause([_]isize{ -4, -2, 1 }));
    try cnf.addClause(Testing.clause([_]isize{ -5, 8, -1 }));
    try cnf.addClause(Testing.clause([_]isize{ -1, -2, -6 }));
    try cnf.addClause(Testing.clause([_]isize{ -4, 1, 7 }));
    try cnf.addClause(Testing.clause([_]isize{ 6, -1, 9 }));
    try cnf.addClause(Testing.clause([_]isize{ -8, 4, -1 }));
    try cnf.addClause(Testing.clause([_]isize{ 7, -6, 1 }));
    try cnf.addClause(Testing.clause([_]isize{ -9, 4, -8 }));
    try cnf.addClause(Testing.clause([_]isize{ -8, 7, 4 }));
    try cnf.addClause(Testing.clause([_]isize{ -7, 2, -5 }));
    try cnf.addClause(Testing.clause([_]isize{ -7, -6, 4 }));
    try cnf.addClause(Testing.clause([_]isize{ -8, -7, 6 }));
    try cnf.addClause(Testing.clause([_]isize{ -4, -5, 1 }));
    try cnf.addClause(Testing.clause([_]isize{ 5, 3, 6 }));
    try cnf.addClause(Testing.clause([_]isize{ -5, 8, -4 }));
    try cnf.addClause(Testing.clause([_]isize{ -2, -6, -1 }));
    try cnf.addClause(Testing.clause([_]isize{ 9, -3, -1 }));
    try cnf.addClause(Testing.clause([_]isize{ 9, -6, -7 }));
    try cnf.addClause(Testing.clause([_]isize{ 4, -3, -5 }));
    try cnf.addClause(Testing.clause([_]isize{ 5, -8, 3 }));
    try cnf.addClause(Testing.clause([_]isize{ 2, 3, -1 }));
    try cnf.addClause(Testing.clause([_]isize{ -8, -5, 4 }));
    try cnf.addClause(Testing.clause([_]isize{ -8, -9, -6 }));
    try cnf.addClause(Testing.clause([_]isize{ 5, -4, 9 }));

    var a = try cnf.satisfiable();
    assert(std.mem.eql(bool, a.?, [_]bool{
        true,
        true,
        true,
        true,
        true,
        false,
        false,
        true,
        false,
        true,
    }));
}

test "pigeon unsat (3 pigeons, 2 holes)" {
    var buffer: [10000]u8 = undefined;
    var allocator = &std.heap.FixedBufferAllocator.init(&buffer).allocator;
    var cnf = CNF.init(allocator);
    defer cnf.deinit();
    try cnf.addClause([_]Literal{Literal{ .term = 0, .sign = true }});

    try cnf.addClause(Testing.clause([_]isize{ 1, 4 }));
    try cnf.addClause(Testing.clause([_]isize{ 2, 5 }));
    try cnf.addClause(Testing.clause([_]isize{ 3, 6 }));

    try cnf.addClause(Testing.clause([_]isize{ -1, -2 }));
    try cnf.addClause(Testing.clause([_]isize{ -1, -3 }));
    try cnf.addClause(Testing.clause([_]isize{ -2, -3 }));

    try cnf.addClause(Testing.clause([_]isize{ -4, -5 }));
    try cnf.addClause(Testing.clause([_]isize{ -4, -6 }));
    try cnf.addClause(Testing.clause([_]isize{ -5, -6 }));

    var a = try cnf.satisfiable();
    assert(a == null);
}

test "pigeon unsat (4 pigeons, 3 holes)" {
    var buffer: [10000]u8 = undefined;
    var allocator = &std.heap.FixedBufferAllocator.init(&buffer).allocator;
    var cnf = CNF.init(allocator);
    defer cnf.deinit();
    Testing.pigeon(&cnf, 4, 3);
    var a = try cnf.satisfiable();
    assert(a == null);
}

test "pigeon unsat (5 pigeons, 5 holes)" {
    var buffer: [100000]u8 = undefined;
    var allocator = &std.heap.FixedBufferAllocator.init(&buffer).allocator;
    var cnf = CNF.init(allocator);
    defer cnf.deinit();
    Testing.pigeon(&cnf, 5, 5);
    var a = try cnf.satisfiable();
    assert(a != null);
}

test "pigeon unsat (5 pigeons, 4 holes)" {
    var buffer: [100000]u8 = undefined;
    var allocator = &std.heap.FixedBufferAllocator.init(&buffer).allocator;
    var cnf = CNF.init(allocator);
    defer cnf.deinit();
    Testing.pigeon(&cnf, 5, 4);
    var a = try cnf.satisfiable();
    assert(a == null);
}

test "pigeon unsat (6 pigeons, 5 holes)" {
    var buffer: [1000000]u8 = undefined;
    var allocator = &std.heap.FixedBufferAllocator.init(&buffer).allocator;
    var cnf = CNF.init(allocator);
    defer cnf.deinit();
    Testing.pigeon(&cnf, 6, 5);
    var a = try cnf.satisfiable();
    assert(a == null);
}

test "pigeon unsat (7 pigeons, 6 holes)" {
    var buffer: [10000000]u8 = undefined;
    var allocator = &std.heap.FixedBufferAllocator.init(&buffer).allocator;
    var cnf = CNF.init(allocator);
    defer cnf.deinit();
    Testing.pigeon(&cnf, 7, 6);
    var a = try cnf.satisfiable();
    assert(a == null);
}

test "unsat example" {
    var buffer: [100000]u8 = undefined;
    var allocator = &std.heap.FixedBufferAllocator.init(&buffer).allocator;
    var cnf = CNF.init(allocator);
    defer cnf.deinit();
    try cnf.addClause([_]Literal{Literal{ .term = 1, .sign = true }});

    try cnf.addClause(Testing.clause([_]isize{ -3, 9, -6 }));
    try cnf.addClause(Testing.clause([_]isize{ 2, 1, 8 }));
    try cnf.addClause(Testing.clause([_]isize{ -6, 4, 2 }));
    try cnf.addClause(Testing.clause([_]isize{ 8, -7, 1 }));
    try cnf.addClause(Testing.clause([_]isize{ 4, -3, -1 }));
    try cnf.addClause(Testing.clause([_]isize{ -1, 6, -9 }));
    try cnf.addClause(Testing.clause([_]isize{ -2, -3, 6 }));
    try cnf.addClause(Testing.clause([_]isize{ 7, -1, -8 }));
    try cnf.addClause(Testing.clause([_]isize{ -2, -6, 7 }));
    try cnf.addClause(Testing.clause([_]isize{ 9, -5, -3 }));
    try cnf.addClause(Testing.clause([_]isize{ -1, 6, -4 }));
    try cnf.addClause(Testing.clause([_]isize{ 9, 3, 8 }));
    try cnf.addClause(Testing.clause([_]isize{ 1, 6, 4 }));
    try cnf.addClause(Testing.clause([_]isize{ 9, -2, -4 }));
    try cnf.addClause(Testing.clause([_]isize{ 5, -2, -4 }));
    try cnf.addClause(Testing.clause([_]isize{ 7, 4, 3 }));
    try cnf.addClause(Testing.clause([_]isize{ -1, -7, 2 }));
    try cnf.addClause(Testing.clause([_]isize{ -4, -7, 9 }));
    try cnf.addClause(Testing.clause([_]isize{ 4, 3, 5 }));
    try cnf.addClause(Testing.clause([_]isize{ -8, 7, 4 }));
    try cnf.addClause(Testing.clause([_]isize{ -1, -5, -4 }));
    try cnf.addClause(Testing.clause([_]isize{ 2, -1, 5 }));
    try cnf.addClause(Testing.clause([_]isize{ -5, 1, -6 }));
    try cnf.addClause(Testing.clause([_]isize{ -9, -5, -8 }));
    try cnf.addClause(Testing.clause([_]isize{ -2, -1, 5 }));
    try cnf.addClause(Testing.clause([_]isize{ -2, -8, 6 }));
    try cnf.addClause(Testing.clause([_]isize{ -4, 3, -6 }));
    try cnf.addClause(Testing.clause([_]isize{ 6, -1, 5 }));
    try cnf.addClause(Testing.clause([_]isize{ 3, -4, 6 }));
    try cnf.addClause(Testing.clause([_]isize{ 7, -8, -3 }));
    try cnf.addClause(Testing.clause([_]isize{ -8, 9, 2 }));
    try cnf.addClause(Testing.clause([_]isize{ 8, -5, -9 }));
    try cnf.addClause(Testing.clause([_]isize{ 6, -9, -2 }));
    try cnf.addClause(Testing.clause([_]isize{ -4, 6, 7 }));
    try cnf.addClause(Testing.clause([_]isize{ -8, -9, 4 }));
    try cnf.addClause(Testing.clause([_]isize{ 5, -4, 9 }));
    try cnf.addClause(Testing.clause([_]isize{ 8, 5, 7 }));
    try cnf.addClause(Testing.clause([_]isize{ -2, 4, 1 }));
    try cnf.addClause(Testing.clause([_]isize{ 4, -2, -9 }));
    try cnf.addClause(Testing.clause([_]isize{ -5, -7, 1 }));
    try cnf.addClause(Testing.clause([_]isize{ -1, -7, -6 }));
    try cnf.addClause(Testing.clause([_]isize{ -1, -9, -6 }));
    try cnf.addClause(Testing.clause([_]isize{ 6, -7, -5 }));
    try cnf.addClause(Testing.clause([_]isize{ -5, -1, -9 }));
    try cnf.addClause(Testing.clause([_]isize{ 1, -5, 9 }));
    try cnf.addClause(Testing.clause([_]isize{ 8, -4, 2 }));
    try cnf.addClause(Testing.clause([_]isize{ 6, -7, -2 }));
    try cnf.addClause(Testing.clause([_]isize{ 9, 2, 5 }));
    try cnf.addClause(Testing.clause([_]isize{ 5, 9, -6 }));
    try cnf.addClause(Testing.clause([_]isize{ -1, 6, 2 }));
    try cnf.addClause(Testing.clause([_]isize{ 3, -2, 9 }));
    try cnf.addClause(Testing.clause([_]isize{ -7, 1, -5 }));
    try cnf.addClause(Testing.clause([_]isize{ -6, 9, 1 }));
    try cnf.addClause(Testing.clause([_]isize{ 9, -1, 6 }));
    try cnf.addClause(Testing.clause([_]isize{ -6, 3, -5 }));
    try cnf.addClause(Testing.clause([_]isize{ 6, 4, -9 }));
    try cnf.addClause(Testing.clause([_]isize{ -1, 3, 5 }));
    try cnf.addClause(Testing.clause([_]isize{ 6, 9, -2 }));
    try cnf.addClause(Testing.clause([_]isize{ -5, -7, -4 }));
    try cnf.addClause(Testing.clause([_]isize{ 7, -6, -2 }));

    var a = try cnf.satisfiable();
    assert(a == null);
}
