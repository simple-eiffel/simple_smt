note
	description: "[
		Facade for simple_smt: a native Eiffel binding to the Z3 SMT solver.

		Build formulas over integers, reals, and booleans; assume them; decide
		satisfiability; extract models; and -- the headline -- prove a conjecture
		(assert its negation and check for unsat).

		Z3 is the trusted oracle; this facade's only claim is faithful translation
		of the Eiffel expression tree into Z3's AST. The test suite grounds that
		claim by proving known theorems and refuting known non-theorems.

		Usage:
			create smt.make
			x := smt.int_const ("x"); z := smt.int_value (0); o := smt.int_value (1)
			-- prove:  x >= 0  implies  x + 1 > 0
			if smt.prove (x.at_least (z).implies (x.plus (o).greater (z))) then
				print ("THEOREM%N")
			end
	]"
	author: "Larry Rix"

class
	SIMPLE_SMT

create
	make

feature {NONE} -- Initialization

	make
			-- Create a solver context ready for use.
		do
			create context.make
			solver := context.new_solver
		end

feature -- Access

	context: SMT_CONTEXT
			-- The underlying Z3 context (expression factory).

	solver: SMT_SOLVER
			-- The active solver.

feature -- Expression builders

	int_const (a_name: STRING): SMT_EXPR
			-- Integer variable `a_name'.
		require
			name_not_empty: not a_name.is_empty
		do
			Result := context.int_const (a_name)
		end

	real_const (a_name: STRING): SMT_EXPR
			-- Real variable `a_name'.
		require
			name_not_empty: not a_name.is_empty
		do
			Result := context.real_const (a_name)
		end

	bool_const (a_name: STRING): SMT_EXPR
			-- Boolean variable `a_name'.
		require
			name_not_empty: not a_name.is_empty
		do
			Result := context.bool_const (a_name)
		end

	int_value (a_value: INTEGER): SMT_EXPR
			-- Integer literal `a_value'.
		do
			Result := context.int_value (a_value)
		end

	real_value (a_literal: STRING): SMT_EXPR
			-- Real literal `a_literal' (e.g. "1/2").
		require
			literal_not_empty: not a_literal.is_empty
		do
			Result := context.real_value (a_literal)
		end

	true_expr: SMT_EXPR
			-- Boolean true.
		do
			Result := context.true_expr
		end

	false_expr: SMT_EXPR
			-- Boolean false.
		do
			Result := context.false_expr
		end

feature -- Assertions & decision

	assume (a_formula: SMT_EXPR)
			-- Add `a_formula' to the assertion set.
		require
			same_context: a_formula.context = context
		do
			solver.assert_formula (a_formula)
		end

	is_satisfiable: BOOLEAN
			-- Is the current assertion set satisfiable?
		do
			Result := solver.is_satisfiable
		end

	is_unsatisfiable: BOOLEAN
			-- Is the current assertion set unsatisfiable?
		do
			Result := solver.is_unsatisfiable
		end

	is_unknown: BOOLEAN
			-- Did the last decision return unknown?
		do
			Result := solver.last_check = solver.Undecided
		end

	model_value (a_expr: SMT_EXPR): STRING
			-- Value of `a_expr' in the current satisfying model ("" if none).
		require
			same_context: a_expr.context = context
		do
			create Result.make_empty
			if solver.last_check = solver.Sat and then attached solver.model as al_m then
				Result := al_m.value_of (a_expr)
				al_m.dispose_model
			end
		ensure
			result_attached: Result /= Void
		end

feature -- Proving

	prove (a_conjecture: SMT_EXPR): BOOLEAN
			-- Is `a_conjecture' valid (true for all values)? Proven by asserting
			-- its negation and checking for unsat. Leaves the assertion set unchanged.
		require
			same_context: a_conjecture.context = context
		do
			solver.push
			solver.assert_formula (a_conjecture.negated)
			Result := solver.is_unsatisfiable
			solver.pop
		ensure
			assertions_unchanged: solver.assertion_count = old solver.assertion_count
		end

	refutation (a_conjecture: SMT_EXPR): STRING
			-- If `a_conjecture' is NOT valid, a textual counter-model (values that
			-- make it false); "" if it is valid (no counterexample exists).
		require
			same_context: a_conjecture.context = context
		local
			l_found: BOOLEAN
		do
			create Result.make_empty
			solver.push
			solver.assert_formula (a_conjecture.negated)
			l_found := solver.is_satisfiable
			if l_found and then attached solver.model as al_m then
				Result := al_m.to_string_representation
				al_m.dispose_model
			end
			solver.pop
		ensure
			assertions_unchanged: solver.assertion_count = old solver.assertion_count
			result_attached: Result /= Void
		end

feature -- Scoping & output

	push do solver.push end
			-- Save assertion state.

	pop
			-- Restore to the last `push'.
		require
			has_scope: solver.has_open_scope
		do
			solver.pop
		end

	reset
			-- Drop all assertions.
		do
			solver.reset
		end

	to_smtlib: STRING
			-- SMT-LIB2 text of the current assertions.
		do
			Result := solver.to_smtlib
		end

invariant
	context_attached: context /= Void
	solver_attached: solver /= Void
	same_context: solver.context = context

end
