const std = @import("std");
const assert = std.debug.assert;

const LinkAllocator = @import("linkalloc.zig").LinkAllocator;

pub fn log(comptime fmt: []const u8, args: ...) void {
    //std.debug.warn(fmt, args);
}

fn STrie(comptime Value: type) type {
    return struct {
        const Self = @This();
        // TODO(#2746): Remove this wrapper.
        const Wrap = struct {
            wrapped: Self,
        };
        allocator: *std.mem.Allocator,
        leafs: [16]?Value,
        branches: [16]?*Wrap,

        fn init(allocator: *std.mem.Allocator) Self {
            return Self{
                .allocator = allocator,
                .leafs = [_]?Value{null} ** 16,
                .branches = [_]?*Wrap{null} ** 16,
            };
        }

        fn deinit(self: *Self) void {
            for (self.branches) |b| {
                if (b) |branch| {
                    branch.wrapped.deinit();
                    self.allocator.destroy(branch);
                }
            }
        }

        fn put(self: *Self, key: []const u8, value: Value) error{OutOfMemory}!void {
            assert(key.len != 0);
            const i = key[0];
            const i_lo = i & 0b00001111;
            const i_hi = (i & 0b11110000) >> 4;
            if (self.branches[i_hi] == null) {
                var ptr = try self.allocator.create(Wrap);
                ptr.wrapped = Self.init(self.allocator);
                self.branches[i_hi] = ptr;
            }

            if (key.len == 1) {
                self.branches[i_hi].?.wrapped.leafs[i_lo] = value;
            } else {
                if (self.branches[i_hi].?.wrapped.branches[i_lo] == null) {
                    var ptr = try self.allocator.create(Wrap);
                    ptr.wrapped = Self.init(self.allocator);
                    self.branches[i_hi].?.wrapped.branches[i_lo] = ptr;
                }
                try self.branches[i_hi].?.wrapped.branches[i_lo].?.wrapped.put(key[1..], value);
            }
        }

        fn get(self: *Self, key: []const u8) ?*Value {
            assert(key.len != 0);
            const i = key[0];
            const i_lo = i & 0b00001111;
            const i_hi = (i & 0b11110000) >> 4;
            if (self.branches[i_hi]) |b_hi| {
                if (key.len == 1) {
                    if (b_hi.wrapped.leafs[i_lo]) |*leaf| {
                        return leaf;
                    }
                    return null;
                } else {
                    if (b_hi.wrapped.branches[i_lo]) |b| {
                        return b.wrapped.get(key[1..]);
                    }
                    return null;
                }
            }
            return null;
        }

        /// RETURNS whether or not this trie contains a key which is a
        /// subsequence of the given argument.
        fn containsSubsequenceKey(self: *Self, key: []const u8) bool {
            if (key.len == 0) return false;
            for (key) |c, i| {
                const c_lo = c & 0b00001111;
                const c_hi = (c & 0b11110000) >> 4;
                if (self.branches[c_hi]) |b_hi| {
                    if (b_hi.wrapped.leafs[c_lo]) |_| return true;
                    if (b_hi.wrapped.branches[c_lo]) |b_lo| {
                        if (b_lo.wrapped.containsSubsequenceKey(key[i + 1 ..])) return true;
                    }
                }
            }
            return false;
        }
    };
}

test "STrie simple" {
    var buffer: [99000]u8 = undefined;
    var linked = LinkAllocator.init(buffer[0..]);
    defer assert(linked.isEmpty());
    var allocator = &linked.allocator;
    var trie = STrie(u8).init(allocator);
    defer trie.deinit();
    assert(trie.get("hi") == null);
    try trie.put("hello", 7);
    assert(trie.get("hello").?.* == 7);
    assert(trie.get("hellp") == null);
    assert(trie.get("hellop") == null);

    try trie.put("cat", 1);
    assert(trie.containsSubsequenceKey("cat"));
    assert(!trie.containsSubsequenceKey("ct"));
    assert(!trie.containsSubsequenceKey("ca"));
    assert(!trie.containsSubsequenceKey("at"));
    assert(!trie.containsSubsequenceKey("c"));
    assert(!trie.containsSubsequenceKey("cta"));
    assert(!trie.containsSubsequenceKey("cc"));
    assert(!trie.containsSubsequenceKey("ll"));
    assert(!trie.containsSubsequenceKey("lll"));
    assert(trie.containsSubsequenceKey("hellocat"));
    assert(trie.containsSubsequenceKey("ccaatt"));
    assert(trie.containsSubsequenceKey("zczaztz"));
    assert(trie.containsSubsequenceKey("hellop"));
}

fn varintEncode(n: usize, out: *std.ArrayList(u8)) !void {
    var k = n;
    while (true) {
        if (k < 128) {
            try out.append(@intCast(u8, k));
            return;
        } else {
            try out.append(128 + @intCast(u8, k & 127));
            k = k / 128;
        }
    }
}

pub const CNF = struct {
    const TermInfo = struct {
        /// Index of clauses satisfied by a `true` assignment.
        clauses_positive: std.ArrayList(usize),

        /// Index of clauses satisfied by a `false` assignment.
        clauses_negative: std.ArrayList(usize),

        preprocessing_negated: bool,

        /// false when this term was added by an external user
        /// true when this was added internally (e.g., for symmetry breaking)
        internal_term: bool,

        fn init(allocator: *std.mem.Allocator, internal_term: bool) TermInfo {
            return TermInfo{
                .clauses_positive = std.ArrayList(usize).init(allocator),
                .clauses_negative = std.ArrayList(usize).init(allocator),
                .preprocessing_negated = false,
                .internal_term = internal_term,
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

    const Clause = struct {
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

        fn invert(self: *Clause, term: usize) void {
            for (self.literals) |*literal| {
                if (literal.term == term) {
                    literal.sign = !literal.sign;
                }
            }
        }

        const Source = enum {
            Problem,
            Conflict,
            SymmetryBreaking,
        };

        literals: []Literal,
        source: Source,
    };

    general_allocator: *std.mem.Allocator,
    clause_allocator: std.heap.ArenaAllocator,
    clauses: std.ArrayList(Clause),
    term_info: std.ArrayList(TermInfo),
    conflict: std.ArrayList(usize),
    diagnose_tmp: std.ArrayList(usize),

    /// Creates an empty clause database (with no terms and no clauses).
    pub fn init(allocator: *std.mem.Allocator) CNF {
        return CNF{
            .general_allocator = allocator,
            .clause_allocator = std.heap.ArenaAllocator.init(allocator),
            .clauses = std.ArrayList(Clause).init(allocator),
            .term_info = std.ArrayList(TermInfo).init(allocator),
            .conflict = std.ArrayList(usize).init(allocator),
            .diagnose_tmp = std.ArrayList(usize).init(allocator),
        };
    }

    pub fn deinit(self: *CNF) void {
        self.clause_allocator.deinit();
        self.clauses.deinit();
        for (self.term_info.toSlice()) |info| {
            info.deinit();
        }
        self.term_info.deinit();
        self.conflict.deinit();
        self.diagnose_tmp.deinit();
    }

    fn vendVariable(self: *CNF, internal: bool) !usize {
        var id = self.term_info.count();
        try self.term_info.append(TermInfo.init(self.allocator, internal));
        return id;
    }

    /// REQUIRES that automorphism actually is an automorphism
    fn learnAutomorphismClauses(self: *CNF, automorphism: []const usize) !void {
        // See "Symmetry-breaking predicates for search problems." (Crawford, Ginsberg, Luks, Roy, 1996)
        var same_variables = std.ArrayList(usize).init(self.allocator);
        defer same_variables.deinit();

        for (automorphism) |_, i| {
            if (automorphism[i] != i) {
                var clause = self.allocator.alloc(Literal, same_variables.count() + 2);
                self.internalAddClause(clause) catch |e| {
                    self.allocator.free(clause);
                    return e;
                };

                // (all same) -> (v[i] < v[a[i]])
                for (same_variables.toSlice()) |v, k| {
                    clause[k] = Literal{ .term = v, .sign = false };
                }
                clause[clause.len - 2] = Literal{ .term = i, .sign = true };
                clause[clause.len - 1] = Literal{ .term = automorphism[i], .sign = false };

                // (a and b) -> s // ~a or ~b or s
                // (~a and ~b) -> s // a or b or s
                // (s and a) -> b // ~s or ~a or b
                // (s and ~a) -> ~b // ~s or a or ~b
                var s = try .self.vendVariable(true);
                try same_variables.append(v);

                var c1 = try self.clause_allocator.allocator.alloc(Literal, 3);
                var c1_saved = false;
                errdefer if (!c1_saved) self.clause_allocator.allocator.free(c1);
                var c2 = try self.clause_allocator.allocator.alloc(Literal, 3);
                var c2_saved = false;
                errdefer if (!c2_saved) self.clause_allocator.allocator.free(c2);
                var c3 = try self.clause_allocator.allocator.alloc(Literal, 3);
                var c3_saved = false;
                errdefer if (!c3_saved) self.clause_allocator.allocator.free(c3);
                var c4 = try self.clause_allocator.allocator.alloc(Literal, 3);
                var c4_saved = false;
                errdefer if (!c4_saved) self.clause_allocator.allocator.free(c4);

                const a = i;
                const b = automorphism[i];

                c1[0] = Literal.negative(a);
                c1[1] = Literal.negative(b);
                c1[2] = Literal.positive(s);

                c2[0] = Literal.positive(a);
                c2[1] = Literal.positive(b);
                c2[2] = Literal.positive(s);

                c3[0] = Literal.negative(a);
                c3[1] = Literal.positive(b);
                c3[2] = Literal.negative(s);

                c4[0] = Literal.positive(a);
                c4[1] = Literal.positive(b);
                c4[2] = Literal.negative(s);

                try self.internalAddClause(c1, Clause.Source.SymmetryBreaking);
                c1_saved = true;
                try self.internalAddClause(c2, Clause.Source.SymmetryBreaking);
                c2_saved = true;
                try self.internalAddClause(c3, Clause.Source.SymmetryBreaking);
                c3_saved = true;
                try self.internalAddClause(c4, Clause.Source.SymmetryBreaking);
                c4_saved = true;
            }
        }
    }

    /// RETURNS whether or not the given mapping is an automorphism (self-isomorphism).
    fn checkProposedAutomorphism(self: *const CNF, automorphism: []const usize) !bool {
        assert(automorphism.len == self.term_info.count());

        var clauses_by_length = std.ArrayList(std.ArrayList(usize)).init(self.general_allocator);
        defer {
            for (clauses_by_length.toSlice()) |arr| {
                arr.deinit();
            }
            clauses_by_length.deinit();
        }

        // Collect a set of clauses in the original CNF.
        var key_list = std.ArrayList(u8).init(self.general_allocator);
        defer key_list.deinit();
        var clause_trie = STrie(bool).init(self.general_allocator);
        defer clause_trie.deinit();
        for (self.clauses.toSlice()) |clause| {
            key_list.shrink(0);
            std.sort.sort(Literal, clause.literals, Literal.lessThan);
            for (clause.literals) |literal| {
                try varintEncode(literal.term * 2 + @boolToInt(literal.sign), &key_list);
            }
            try clause_trie.put(key_list.toSlice(), true);
        }

        // Check if the mappings are in the set.
        var rearr = std.ArrayList(Literal).init(self.general_allocator);
        defer rearr.deinit();
        for (self.clauses.toSlice()) |clause| {
            rearr.shrink(0);
            try rearr.appendSlice(clause.literals);
            for (rearr.toSlice()) |*literal| {
                literal.term = automorphism[literal.term];
            }
            std.sort.sort(Literal, rearr.toSlice(), Literal.lessThan);
            key_list.shrink(0);
            for (rearr.toSlice()) |literal| {
                try varintEncode(literal.term * 2 + @boolToInt(literal.sign), &key_list);
            }

            if (!clause_trie.containsSubsequenceKey(key_list.toSlice())) {
                // This clause is not preserved by the mapping.
                return false;
            }
        }

        // Every clause is preseved by the autmorphism.
        // TODO: Assumes that automorphism is a permutation (no dupliate elements)
        return true;
    }

    fn preprocessClauses(self: *CNF) error{}!void {
        if (self.term_info.count() < 1 << 24) {
            // It's better to not attempt to preprocess small CNFs.
            return;
        }

        // 1) Attempt to normalize the sign of all terms.
        // Every term should appear more often negatively than positively.
        // TODO: Break ties.
        const Counts = struct {
            positive: usize,
            negative: usize,
        };

        // var terms_by_count = PTrie(std.ArrayList(usize)).init(self.allocator);
        for (self.term_info.toSlice()) |*info, term| {
            if (info.clauses_positive.count() > info.clauses_negative.count()) {
                // Swap.
                log("Swapping term x{}, {}", term, info);
                info.preprocessing_negated = !info.preprocessing_negated;
                var was_positive = info.clauses_positive;
                info.clauses_positive = info.clauses_negative;
                info.clauses_negative = was_positive;
                var clauses = self.clauses.toSlice();
                for (info.clauses_positive.toSlice()) |ci| {
                    clauses[ci].invert(term);
                }
                for (info.clauses_negative.toSlice()) |ci| {
                    clauses[ci].invert(term);
                }
            }

            // var count = IPair{
            //     .left = info.clauses_positive.count(),
            //     .right = info.clauses_negative.count(),
            // };
            // if (terms_by_count.get(count) == null) {
            //     try terms_by_count.put(count, std.ArrayList(usize).init(self.allocator));
            // }
            // try terms_by_count.get(count).?.append(term);
        }

        // TODO: Find redundant (subsumed) clauses and remove them.
        // TODO: Simplify using unit clauses.

        // Find interchangeable pairs of variables.
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
        var seen = try self.general_allocator.alloc(bool, assignment.len);
        defer self.general_allocator.free(seen);
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
        defer log("@ <<<<\n\n");
        log("@ =" ** 80 ++ "\n");
        log("@ # clauses at beginning: {}\n", self.clauses.count());
        defer log("@ # clauses at end: {}\n", self.clauses.count());

        try self.preprocessClauses();

        var assignment = try self.general_allocator.alloc(?Assignment, self.term_info.count());
        defer self.general_allocator.free(assignment);
        for (assignment) |_, i| {
            assignment[i] = null;
        }

        // Preprocess the input:
        // Find unit clauses and pure literals.
        var unit_literals = std.ArrayList(Assignment).init(self.general_allocator);
        defer unit_literals.deinit();
        const SignCounts = struct {
            positive: usize,
            negative: usize,
        };
        var sign_counts_list = std.ArrayList(SignCounts).init(self.general_allocator);
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
                log("@ Unit: {}\n", branch);
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
                log("@ Choice: {} (through {})\n", branch, assigned_through);
            }

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
                        var conflict_clause = try self.clause_allocator.allocator.alloc(Literal, self.conflict.count());
                        errdefer self.clause_allocator.allocator.free(conflict_clause); // TODO: This does nothing
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
                            self.clause_allocator.allocator.free(conflict_clause); // TODO: This does nothing
                            // A contradiction has been reached.
                            return null;
                        }

                        // Add the clause, then reset the decision level, assignment stack, and unit clause set.
                        try self.internalAddClause(conflict_clause, Clause.Source.Conflict);
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
        var out = try self.general_allocator.alloc(bool, assignment.len);
        for (assignment) |a, i| {
            out[i] = a.?.assignment != self.term_info.at(i).preprocessing_negated;
        }
        return out;
    }

    fn internalAddClause(self: *CNF, literals: []Literal, source: Clause.Source) !void {
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
            .source = source,
            .literals = literals,
        });
    }

    /// Adds a clause to this CNF clause database.
    /// REQUIRES literals is not empty.
    pub fn addClause(self: *CNF, literals: []const Literal) !void {
        assert(literals.len != 0);

        // Grow the set of terms as needed.
        for (literals) |literal| {
            while (literal.term >= self.term_info.count()) {
                var term_info = TermInfo.init(self.general_allocator, false);
                try self.term_info.append(term_info);
            }
            assert(!self.term_info.at(literal.term).internal_term);
        }

        // TODO: Check for duplicates, and tautological clauses
        var copy = try self.clause_allocator.allocator.alloc(Literal, literals.len);
        errdefer self.clause_allocator.allocator.free(copy); // TODO: This does nothing
        std.mem.copy(Literal, copy, literals);

        try self.internalAddClause(copy, Clause.Source.Problem);
    }
};

pub const Literal = struct {
    // This literal is satisfied when the term is assigned the truth value of
    // `sign`. For example,
    // "x_0" is (0, true).
    // "~x_9" is (9, false).
    term: usize,
    sign: bool,

    fn positive(term: usize) Literal {
        return Literal{ .term = term, .sign = true };
    }

    fn negative(term: usize) Literal {
        return Literal{ .term = term, .sign = false };
    }

    fn lessThan(a: Literal, b: Literal) bool {
        if (a.term != b.term) {
            return a.term < b.term;
        }
        return !a.sign and b.sign;
    }
};

test "sat (x)" {
    var buffer: [1000000]u8 = undefined;
    var linked = LinkAllocator.init(buffer[0..]);
    defer assert(linked.isEmpty());
    var allocator = &linked.allocator;
    var cnf = CNF.init(allocator);
    defer cnf.deinit();
    try cnf.addClause([_]Literal{Literal{ .term = 0, .sign = true }});

    const sat = (try cnf.satisfiable()).?;
    assert(sat.len == 1);
    assert(sat[0] == true);
    allocator.free(sat);
}

test "unsat (x) and (~x)" {
    var buffer: [1000000]u8 = undefined;
    var linked = LinkAllocator.init(buffer[0..]);
    defer assert(linked.isEmpty());
    var allocator = &linked.allocator;
    var cnf = CNF.init(allocator);
    defer cnf.deinit();
    try cnf.addClause([_]Literal{Literal{ .term = 0, .sign = true }});
    try cnf.addClause([_]Literal{Literal{ .term = 0, .sign = false }});

    const sat = try cnf.satisfiable();
    assert(sat == null);
}

test "sat (~x or y) and (x or ~y)" {
    var buffer: [1000000]u8 = undefined;
    var linked = LinkAllocator.init(buffer[0..]);
    defer assert(linked.isEmpty());
    var allocator = &linked.allocator;
    var cnf = CNF.init(allocator);
    defer cnf.deinit();
    try cnf.addClause([_]Literal{ Literal{ .term = 1, .sign = false }, Literal{ .term = 0, .sign = true } });
    try cnf.addClause([_]Literal{ Literal{ .term = 1, .sign = true }, Literal{ .term = 0, .sign = false } });

    const sat = try cnf.satisfiable();
    assert(sat != null);
    assert(sat.?.len == 2);
    assert(sat.?[0] == sat.?[1]);
    allocator.free(sat.?);
}

test "sat (x or y) and (~x or ~y)" {
    var buffer: [1000000]u8 = undefined;
    var linked = LinkAllocator.init(buffer[0..]);
    defer assert(linked.isEmpty());
    var allocator = &linked.allocator;
    var cnf = CNF.init(allocator);
    defer cnf.deinit();
    try cnf.addClause([_]Literal{ Literal{ .term = 1, .sign = true }, Literal{ .term = 0, .sign = true } });
    try cnf.addClause([_]Literal{ Literal{ .term = 1, .sign = false }, Literal{ .term = 0, .sign = false } });

    const sat = try cnf.satisfiable();
    assert(sat != null);
    assert(sat.?.len == 2);
    assert(sat.?[0] != sat.?[1]);
    allocator.free(sat.?);
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
                    // TODO(#3095):
                    const lit0 = Literal{ .term = pigeons * hole + p_a, .sign = false };
                    literals[0] = lit0;
                    const lit1 = Literal{ .term = pigeons * hole + p_b, .sign = false };
                    literals[1] = lit1;
                    cnf.addClause(literals[0..2]) catch unreachable;
                }
            }
        }
    }
};

test "example" {
    var buffer: [10000000]u8 = undefined;
    var linked = LinkAllocator.init(buffer[0..]);
    defer assert(linked.isEmpty());
    var allocator = &linked.allocator;
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
    allocator.free(a.?);
}

test "pigeon unsat (3 pigeons, 2 holes)" {
    var buffer: [1000000]u8 = undefined;
    var linked = LinkAllocator.init(buffer[0..]);
    defer assert(linked.isEmpty());
    var allocator = &linked.allocator;
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
    var buffer: [1000000]u8 = undefined;
    var linked = LinkAllocator.init(buffer[0..]);
    defer assert(linked.isEmpty());
    var allocator = &linked.allocator;
    var cnf = CNF.init(allocator);
    defer cnf.deinit();
    Testing.pigeon(&cnf, 4, 3);
    var a = try cnf.satisfiable();
    assert(a == null);
}

test "pigeon automorphism (4 pigeons, 3 holes)" {
    var buffer: [1000000]u8 = undefined;
    var linked = LinkAllocator.init(buffer[0..]);
    defer assert(linked.isEmpty());
    var allocator = &linked.allocator;
    var cnf = CNF.init(allocator);
    defer cnf.deinit();
    Testing.pigeon(&cnf, 4, 3);

    var mapping = [_]usize{
        0,
        1,
        2,
        3,
        4,
        5,
        6,
        7,
        8,
        9,
        10,
        11,
    };
    assert(try cnf.checkProposedAutomorphism(mapping[0..]));

    mapping[0] = 1;
    mapping[1] = 0;
    assert(!try cnf.checkProposedAutomorphism(mapping[0..]));
    mapping[0] = 0;
    mapping[1] = 1;

    // Swap (0, 4, 8) with (3, 7, 11)
    mapping[0] = 3;
    mapping[4] = 7;
    mapping[8] = 11;
    mapping[3] = 0;
    mapping[7] = 4;
    mapping[11] = 8;
    assert(try cnf.checkProposedAutomorphism(mapping[0..]));
    mapping[1] = 2;
    mapping[2] = 1;
    assert(!try cnf.checkProposedAutomorphism(mapping[0..]));
}

test "pigeon unsat (5 pigeons, 5 holes)" {
    var buffer: [10000000]u8 = undefined;
    var linked = LinkAllocator.init(buffer[0..]);
    defer assert(linked.isEmpty());
    var allocator = &linked.allocator;
    var cnf = CNF.init(allocator);
    defer cnf.deinit();
    Testing.pigeon(&cnf, 5, 5);
    var a = try cnf.satisfiable();
    assert(a != null);
    allocator.free(a.?);
}

test "pigeon unsat (5 pigeons, 4 holes)" {
    var buffer: [10000000]u8 = undefined;
    var linked = LinkAllocator.init(buffer[0..]);
    defer assert(linked.isEmpty());
    var allocator = &linked.allocator;
    var cnf = CNF.init(allocator);
    defer cnf.deinit();
    Testing.pigeon(&cnf, 5, 4);
    var a = try cnf.satisfiable();
    assert(a == null);
}

test "pigeon unsat (6 pigeons, 5 holes)" {
    var buffer: [10000000]u8 = undefined;
    var linked = LinkAllocator.init(buffer[0..]);
    defer assert(linked.isEmpty());
    var allocator = &linked.allocator;
    var cnf = CNF.init(allocator);
    defer cnf.deinit();
    Testing.pigeon(&cnf, 6, 5);
    var a = try cnf.satisfiable();
    assert(a == null);
}

test "pigeon unsat (7 pigeons, 6 holes)" {
    // The FixedBufferAllocator requires about 7.7MB.
    // The LinkAllocator requires about 1.5MB.
    var buffer: [1309600]u8 = undefined;
    var linked = LinkAllocator.init(buffer[0..]);
    defer assert(linked.isEmpty());
    var allocator = &linked.allocator;
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

pub fn main() !void {
    var buffer: [1309600]u8 = undefined;
    var linked = LinkAllocator.init(buffer[0..]);
    defer assert(linked.isEmpty());
    var allocator = &linked.allocator;
    var cnf = CNF.init(allocator);
    defer cnf.deinit();
    Testing.pigeon(&cnf, 7, 6);
    var a = try cnf.satisfiable();
    assert(a == null);
}
