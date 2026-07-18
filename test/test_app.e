note
	description: "Test runner for simple_smt"
	author: "Larry Rix"

class
	TEST_APP

create
	make

feature {NONE} -- Initialization

	make
		local
			tests: LIB_TESTS
		do
			create tests
			io.put_string ("simple_smt test runner%N====================================%N%N")
			passed := 0
			failed := 0

			io.put_string ("Satisfiability%N--------------%N")
			run_test (agent tests.test_trivially_sat, "test_trivially_sat")
			run_test (agent tests.test_contradiction_unsat, "test_contradiction_unsat")
			run_test (agent tests.test_bounded_range_sat_with_model, "test_bounded_range_sat_with_model")

			io.put_string ("%NTheorems (proved)%N-----------------%N")
			run_test (agent tests.test_prove_successor_positive, "test_prove_successor_positive")
			run_test (agent tests.test_prove_add_identity, "test_prove_add_identity")
			run_test (agent tests.test_prove_increment_strictly_greater, "test_prove_increment_strictly_greater")
			run_test (agent tests.test_prove_transitivity, "test_prove_transitivity")
			run_test (agent tests.test_prove_index_bound, "test_prove_index_bound")

			io.put_string ("%NBoolean logic%N-------------%N")
			run_test (agent tests.test_prove_excluded_middle, "test_prove_excluded_middle")
			run_test (agent tests.test_prove_de_morgan, "test_prove_de_morgan")

			io.put_string ("%NRefutation (non-theorems)%N-------------------------%N")
			run_test (agent tests.test_refute_false_conjecture, "test_refute_false_conjecture")
			run_test (agent tests.test_no_false_theorem, "test_no_false_theorem")

			io.put_string ("%NReals vs ints%N-------------%N")
			run_test (agent tests.test_real_half_sat, "test_real_half_sat")
			run_test (agent tests.test_int_half_unsat, "test_int_half_unsat")

			io.put_string ("%NMechanics%N---------%N")
			run_test (agent tests.test_prove_does_not_mutate, "test_prove_does_not_mutate")
			run_test (agent tests.test_push_pop_scoping, "test_push_pop_scoping")
			run_test (agent tests.test_smtlib_emission, "test_smtlib_emission")

			io.put_string ("%N====================================%N")
			io.put_string ("Results: " + passed.out + " passed, " + failed.out + " failed%N")
			if failed > 0 then
				io.put_string ("TESTS FAILED%N")
			else
				io.put_string ("ALL TESTS PASSED%N")
			end
		end

feature {NONE} -- Implementation

	passed, failed: INTEGER

	run_test (a_test: PROCEDURE; a_name: STRING)
		local
			l_retried: BOOLEAN
		do
			if not l_retried then
				a_test.call (Void)
				io.put_string ("  PASS: " + a_name + "%N")
				passed := passed + 1
			end
		rescue
			io.put_string ("  FAIL: " + a_name + "%N")
			failed := failed + 1
			l_retried := True
			retry
		end

end
