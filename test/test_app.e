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

			run_real_world_tests

			io.put_string ("%N====================================%N")
			io.put_string ("Results: " + passed.out + " passed, " + failed.out + " failed%N")
			if failed > 0 then
				io.put_string ("TESTS FAILED%N")
			else
				io.put_string ("ALL TESTS PASSED%N")
			end
		end

	run_real_world_tests
			-- Ecosystem-mined real-world scenarios + AutoProof ACCOUNT reproduction.
		local
			rw: REAL_WORLD_TESTS
		do
			create rw
			io.put_string ("%NReal-world: numeric libs%N------------------------%N")
			run_test (agent rw.test_uniform_mean_between_bounds, "uniform_mean_between_bounds")
			run_test (agent rw.test_binomial_weak_spec_admits_invalid_p, "binomial_weak_spec_admits_invalid_p")
			run_test (agent rw.test_binomial_strong_spec_blocks_invalid_p, "binomial_strong_spec_blocks_invalid_p")
			run_test (agent rw.test_fraction_cross_multiply_transitivity, "fraction_cross_multiply_transitivity")
			run_test (agent rw.test_decimal_split_remainder_sum_identity, "decimal_split_remainder_sum_identity")
			run_test (agent rw.test_fraction_negate_sign_xor, "fraction_negate_sign_xor")

			io.put_string ("%NReal-world: data-structure libs%N-------------------------------%N")
			run_test (agent rw.test_slice_index_safety, "slice_index_safety")
			run_test (agent rw.test_cache_capacity_preserved_via_ite, "cache_capacity_preserved_via_ite")
			run_test (agent rw.test_graph_handshake_even_lemma, "graph_handshake_even_lemma")
			run_test (agent rw.test_graph_handshake_selfloop_violation, "graph_handshake_selfloop_violation")
			run_test (agent rw.test_sorter_is_sorted_alone_is_vacuous, "sorter_is_sorted_alone_is_vacuous")
			run_test (agent rw.test_sorter_full_spec_pins_permutation, "sorter_full_spec_pins_permutation")
			run_test (agent rw.test_json_array_valid_index_excludes_boundaries, "json_array_valid_index_excludes_boundaries")
			run_test (agent rw.test_container_chunked_ceiling_division, "container_chunked_ceiling_division")

			io.put_string ("%NReal-world: systems/format libs%N-------------------------------%N")
			run_test (agent rw.test_base64_encoded_length_multiple_of_four, "base64_encoded_length_multiple_of_four")
			run_test (agent rw.test_base64_length_roundtrip, "base64_length_roundtrip")
			run_test (agent rw.test_iso_day_of_week_equivalence, "iso_day_of_week_equivalence")
			run_test (agent rw.test_seconds_since_midnight_decomposition, "seconds_since_midnight_decomposition")
			run_test (agent rw.test_hour_12_wraparound_range, "hour_12_wraparound_range")
			run_test (agent rw.test_adler32_running_sums_bounded, "adler32_running_sums_bounded")
			run_test (agent rw.test_base64_weak_length_spec_admits_stub, "base64_weak_length_spec_admits_stub")
			run_test (agent rw.test_base64_strong_length_spec_pins_value, "base64_strong_length_spec_pins_value")

			io.put_string ("%NReal-world: classic problems%N----------------------------%N")
			run_test (agent rw.test_pigeonhole_3_into_2, "pigeonhole_3_into_2")
			run_test (agent rw.test_pigeonhole_5_into_4, "pigeonhole_5_into_4")
			run_test (agent rw.test_triangle_3coloring_sat, "triangle_3coloring_sat")
			run_test (agent rw.test_k4_3coloring_unsat, "k4_3coloring_unsat")
			run_test (agent rw.test_latin_square_row_sat, "latin_square_row_sat")
			run_test (agent rw.test_array_bounds_loop_invariant, "array_bounds_loop_invariant")
			run_test (agent rw.test_integer_overflow_bound, "integer_overflow_bound")
			run_test (agent rw.test_max_via_ite_correct, "max_via_ite_correct")
			run_test (agent rw.test_abs_via_ite_correct, "abs_via_ite_correct")
			run_test (agent rw.test_day_of_week_modular_period, "day_of_week_modular_period")
			run_test (agent rw.test_nonlinear_sqrt2_unsat_over_ints, "nonlinear_sqrt2_unsat_over_ints")
			run_test (agent rw.test_nonlinear_sqrt2_sat_over_reals, "nonlinear_sqrt2_sat_over_reals")

			io.put_string ("%NReal-world: AutoProof ACCOUNT reproduction%N------------------------------------------%N")
			run_test (agent rw.test_account_withdraw_invariant_bug, "account_withdraw_invariant_bug")
			run_test (agent rw.test_account_withdraw_decreased_bug, "account_withdraw_decreased_bug")
			run_test (agent rw.test_account_transfer_decreased_bug, "account_transfer_decreased_bug")
			run_test (agent rw.test_account_withdraw_invariant_fixed, "account_withdraw_invariant_fixed")
			run_test (agent rw.test_account_withdraw_decreased_fixed, "account_withdraw_decreased_fixed")
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
