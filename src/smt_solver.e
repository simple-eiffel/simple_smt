note
	description: "[
		A Z3 solver: an assertion set plus check/model/push/pop. Wraps a
		reference-counted Z3_solver.
	]"
	author: "Larry Rix"

class
	SMT_SOLVER

create
	make

feature {NONE} -- Initialization

	make (a_context: SMT_CONTEXT)
			-- Create a solver over `a_context'.
		do
			context := a_context
			solver := context.c_mk_solver (context.context)
			context.c_solver_inc_ref (context.context, solver)
			assertion_count := 0
			last_check := Undecided
		ensure
			context_set: context = a_context
			solver_attached: solver /= default_pointer
		end

feature -- Constants

	Sat: INTEGER = 1
	Unsat: INTEGER = -1
	Undecided: INTEGER = 0
			-- Check outcomes (mirror Z3_lbool).

feature -- Access

	context: SMT_CONTEXT
			-- Owning context.

	solver: POINTER
			-- Z3_solver handle.

	assertion_count: INTEGER
			-- Number of formulas asserted at the current push level base.

	last_check: INTEGER
			-- Outcome of the most recent decision (Sat / Unsat / Undecided).

	has_open_scope: BOOLEAN
			-- Is there a `push'ed scope that `pop' can restore?
		do
			Result := not saved_counts.is_empty
		end

feature -- Assertion

	assert_formula (a_formula: SMT_EXPR)
			-- Add `a_formula' to the assertion set.
		require
			same_context: a_formula.context = context
		do
			context.c_solver_assert (context.context, solver, a_formula.ast)
			assertion_count := assertion_count + 1
		ensure
			counted: assertion_count = old assertion_count + 1
		end

feature -- Decision

	decide: INTEGER
			-- Decide satisfiability of the current assertion set (`check' is an
			-- Eiffel keyword, so the query is named `decide').
		do
			Result := context.c_solver_check (context.context, solver)
			last_check := Result
		ensure
			valid: Result = Sat or Result = Unsat or Result = Undecided
			recorded: last_check = Result
		end

	is_satisfiable: BOOLEAN
			-- Is the current assertion set satisfiable?
		do
			Result := decide = Sat
		end

	is_unsatisfiable: BOOLEAN
			-- Is the current assertion set unsatisfiable (i.e. proven contradictory)?
		do
			Result := decide = Unsat
		end

	model: detachable SMT_MODEL
			-- Satisfying model after a Sat check; Void otherwise.
		require
			was_sat: last_check = Sat
		local
			l_ptr: POINTER
		do
			l_ptr := context.c_solver_get_model (context.context, solver)
			if l_ptr /= default_pointer then
				create Result.make (context, l_ptr)
			end
		end

feature -- Scoping

	push
			-- Save the current assertion state.
		do
			context.c_solver_push (context.context, solver)
			saved_counts.extend (assertion_count)
		end

	pop
			-- Restore the assertion state to the last `push'.
		require
			has_scope: has_open_scope
		do
			context.c_solver_pop (context.context, solver, 1)
			assertion_count := saved_counts.last
			saved_counts.finish
			saved_counts.remove
		end

	reset
			-- Drop all assertions.
		do
			context.c_solver_reset (context.context, solver)
			assertion_count := 0
			saved_counts.wipe_out
			last_check := Undecided
		ensure
			empty: assertion_count = 0
		end

feature -- Output

	to_smtlib: STRING
			-- SMT-LIB2 rendering of the current assertions.
		local
			l_ptr: POINTER
		do
			l_ptr := context.c_solver_to_string (context.context, solver)
			if l_ptr /= default_pointer then
				create Result.make_from_c (l_ptr)
			else
				create Result.make_empty
			end
		ensure
			result_attached: Result /= Void
		end

feature -- Disposal

	dispose_solver
			-- Release the solver.
		do
			if solver /= default_pointer then
				context.c_solver_dec_ref (context.context, solver)
				solver := default_pointer
			end
		end

feature {NONE} -- Implementation

	saved_counts: ARRAYED_LIST [INTEGER]
			-- Assertion counts saved by `push'.
		attribute
			create Result.make (4)
		end

invariant
	context_attached: context /= Void
	last_check_valid: last_check = Sat or last_check = Unsat or last_check = Undecided
	assertion_count_non_negative: assertion_count >= 0

end
