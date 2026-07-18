note
	description: "Tests for simple_smt: real theorems proved, real non-theorems refuted with counter-models"
	author: "Larry Rix"

class
	LIB_TESTS

inherit
	TEST_SET_BASE

feature -- Tests: satisfiability

	test_trivially_sat
			-- x > 5 is satisfiable.
		local
			smt: SIMPLE_SMT
			x: SMT_EXPR
		do
			create smt.make
			x := smt.int_const ("x")
			smt.assume (x.greater (smt.int_value (5)))
			assert ("x>5 is sat", smt.is_satisfiable)
		end

	test_contradiction_unsat
			-- x > 0 and x < 0 is unsatisfiable.
		local
			smt: SIMPLE_SMT
			x: SMT_EXPR
		do
			create smt.make
			x := smt.int_const ("x")
			smt.assume (x.greater (smt.int_value (0)))
			smt.assume (x.less (smt.int_value (0)))
			assert ("x>0 and x<0 is unsat", smt.is_unsatisfiable)
		end

	test_bounded_range_sat_with_model
			-- 5 < x < 8 has a model, and it lies in range.
		local
			smt: SIMPLE_SMT
			x: SMT_EXPR
			l_val: STRING
			l_int: INTEGER
		do
			create smt.make
			x := smt.int_const ("x")
			smt.assume (x.greater (smt.int_value (5)))
			smt.assume (x.less (smt.int_value (8)))
			assert ("sat", smt.is_satisfiable)
			l_val := smt.model_value (x)
			assert ("model non-empty", not l_val.is_empty)
			assert ("model is integer", l_val.is_integer)
			l_int := l_val.to_integer
			assert ("model in (5,8)", l_int > 5 and l_int < 8)
		end

feature -- Tests: proving theorems (negation unsat)

	test_prove_successor_positive
			-- THEOREM: x >= 0  implies  x + 1 > 0.  (the theory-turn example)
		local
			smt: SIMPLE_SMT
			x, zero, one: SMT_EXPR
		do
			create smt.make
			x := smt.int_const ("x")
			zero := smt.int_value (0)
			one := smt.int_value (1)
			assert ("x>=0 -> x+1>0 is valid",
				smt.prove (x.at_least (zero).entails (x.plus (one).greater (zero))))
		end

	test_prove_add_identity
			-- THEOREM: x + 0 = x.
		local
			smt: SIMPLE_SMT
			x: SMT_EXPR
		do
			create smt.make
			x := smt.int_const ("x")
			assert ("x+0=x", smt.prove (x.plus (smt.int_value (0)).is_equal_to (x)))
		end

	test_prove_increment_strictly_greater
			-- THEOREM: x + 1 > x.
		local
			smt: SIMPLE_SMT
			x: SMT_EXPR
		do
			create smt.make
			x := smt.int_const ("x")
			assert ("x+1>x", smt.prove (x.plus (smt.int_value (1)).greater (x)))
		end

	test_prove_transitivity
			-- THEOREM: (x < y and y < z) implies x < z.
		local
			smt: SIMPLE_SMT
			x, y, z: SMT_EXPR
		do
			create smt.make
			x := smt.int_const ("x")
			y := smt.int_const ("y")
			z := smt.int_const ("z")
			assert ("transitivity of <",
				smt.prove (x.less (y).conjoined (y.less (z)).entails (x.less (z))))
		end

	test_prove_index_bound
			-- THEOREM (contract fragment): (1 <= k and k <= n) implies k <= n.
		local
			smt: SIMPLE_SMT
			k, n, one: SMT_EXPR
		do
			create smt.make
			k := smt.int_const ("k")
			n := smt.int_const ("n")
			one := smt.int_value (1)
			assert ("1<=k<=n -> k<=n",
				smt.prove (one.at_most (k).conjoined (k.at_most (n)).entails (k.at_most (n))))
		end

feature -- Tests: boolean logic

	test_prove_excluded_middle
			-- THEOREM: a or not a.
		local
			smt: SIMPLE_SMT
			a: SMT_EXPR
		do
			create smt.make
			a := smt.bool_const ("a")
			assert ("a or not a", smt.prove (a.disjoined (a.negated)))
		end

	test_prove_de_morgan
			-- THEOREM: not (a and b) = (not a or not b).
		local
			smt: SIMPLE_SMT
			a, b: SMT_EXPR
		do
			create smt.make
			a := smt.bool_const ("a")
			b := smt.bool_const ("b")
			assert ("de morgan",
				smt.prove (a.conjoined (b).negated.is_equal_to (a.negated.disjoined (b.negated))))
		end

feature -- Tests: refutation (non-theorems)

	test_refute_false_conjecture
			-- NON-THEOREM: x > 0 is not valid; a counter-model exists.
		local
			smt: SIMPLE_SMT
			x: SMT_EXPR
			l_counter: STRING
		do
			create smt.make
			x := smt.int_const ("x")
			assert ("x>0 is NOT valid", not smt.prove (x.greater (smt.int_value (0))))
			l_counter := smt.refutation (x.greater (smt.int_value (0)))
			assert ("counter-model produced", not l_counter.is_empty)
		end

	test_no_false_theorem
			-- Sanity: a genuine contradiction is not "proved" as a theorem in the wrong direction.
		local
			smt: SIMPLE_SMT
			x: SMT_EXPR
		do
			create smt.make
			x := smt.int_const ("x")
				-- x < x is never true -> not valid.
			assert ("x<x not valid", not smt.prove (x.less (x)))
				-- x = x is always true -> valid.
			assert ("x=x valid", smt.prove (x.is_equal_to (x)))
		end

feature -- Tests: reals vs ints

	test_real_half_sat
			-- Over the reals, 2*x = 1 is satisfiable (x = 1/2).
		local
			smt: SIMPLE_SMT
			x: SMT_EXPR
		do
			create smt.make
			x := smt.real_const ("x")
			smt.assume (x.plus (x).is_equal_to (smt.real_value ("1")))
			assert ("2x=1 sat over reals", smt.is_satisfiable)
		end

	test_int_half_unsat
			-- Over the integers, 2*x = 1 is unsatisfiable.
		local
			smt: SIMPLE_SMT
			x: SMT_EXPR
		do
			create smt.make
			x := smt.int_const ("x")
			smt.assume (x.plus (x).is_equal_to (smt.int_value (1)))
			assert ("2x=1 unsat over ints", smt.is_unsatisfiable)
		end

feature -- Tests: mechanics

	test_prove_does_not_mutate
			-- prove leaves the assertion set untouched.
		local
			smt: SIMPLE_SMT
			x: SMT_EXPR
			l_before: INTEGER
		do
			create smt.make
			x := smt.int_const ("x")
			smt.assume (x.greater (smt.int_value (3)))
			l_before := smt.solver.assertion_count
			if smt.prove (x.plus (smt.int_value (1)).greater (x)) then end
			assert ("assertion count unchanged", smt.solver.assertion_count = l_before)
			assert ("still sat after prove", smt.is_satisfiable)
		end

	test_push_pop_scoping
			-- pop restores a state made unsat inside the scope.
		local
			smt: SIMPLE_SMT
			x: SMT_EXPR
		do
			create smt.make
			x := smt.int_const ("x")
			smt.assume (x.greater (smt.int_value (0)))
			assert ("sat before scope", smt.is_satisfiable)
			smt.push
			smt.assume (x.less (smt.int_value (0)))
			assert ("unsat inside scope", smt.is_unsatisfiable)
			smt.pop
			assert ("sat again after pop", smt.is_satisfiable)
		end

	test_smtlib_emission
			-- to_smtlib renders the asserted formula.
		local
			smt: SIMPLE_SMT
			x: SMT_EXPR
			l_text: STRING
		do
			create smt.make
			x := smt.int_const ("x")
			smt.assume (x.greater (smt.int_value (7)))
			l_text := smt.to_smtlib
			assert ("smtlib mentions x", l_text.has_substring ("x"))
		end

end
