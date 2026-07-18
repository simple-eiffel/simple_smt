note
	description: "[
		Real-world stress tests for simple_smt, mined from actual simple_*
		ecosystem contracts and classic verification problems by a fleet of
		research agents. Each is grounded in a real feature/file or a canonical
		problem with a certain verdict. Includes a reproduction of the AutoProof
		ACCOUNT tutorial: simple_smt refutes the same withdraw/transfer bugs the
		MIT verifier flags, then proves the fixed versions.
	]"
	author: "Larry Rix"

class
	REAL_WORLD_TESTS

inherit
	TEST_SET_BASE

feature -- Numeric / math libraries

	test_uniform_mean_between_bounds
			-- simple_probability UNIFORM_DISTRIBUTION.mean midpoint lies within [min,max].
		local
			smt: SIMPLE_SMT
			amin, amax, mean, two: SMT_EXPR
		do
			create smt.make
			amin := smt.real_const ("amin"); amax := smt.real_const ("amax"); mean := smt.real_const ("mean")
			two := smt.real_value ("2")
			assert ("mean in [min,max]",
				smt.prove (amin.less (amax).conjoined (two.times (mean).is_equal_to (amin.plus (amax)))
					.entails (amin.at_most (mean).conjoined (mean.at_most (amax)))))
		end

	test_binomial_weak_spec_admits_invalid_p
			-- NON-VACUITY: BINOMIAL with only p<=1 (mutant) lets p=-5 through.
		local
			smt: SIMPLE_SMT
			n, p: SMT_EXPR
		do
			create smt.make
			n := smt.int_const ("n"); p := smt.real_const ("p")
			smt.assume (n.greater (smt.int_value (0)))
			smt.assume (p.at_most (smt.real_value ("1")))
			smt.assume (p.less (smt.real_value ("0")).disjoined (p.greater (smt.real_value ("1"))))
			assert ("weak precondition is satisfiable by invalid p", smt.is_satisfiable)
		end

	test_binomial_strong_spec_blocks_invalid_p
			-- The REAL BINOMIAL contract (0<=p<=1) rules the counterexample out.
		local
			smt: SIMPLE_SMT
			n, p: SMT_EXPR
		do
			create smt.make
			n := smt.int_const ("n"); p := smt.real_const ("p")
			smt.assume (n.greater (smt.int_value (0)))
			smt.assume (p.at_least (smt.real_value ("0")))
			smt.assume (p.at_most (smt.real_value ("1")))
			smt.assume (p.less (smt.real_value ("0")).disjoined (p.greater (smt.real_value ("1"))))
			assert ("strong precondition is unsatisfiable with invalid p", smt.is_unsatisfiable)
		end

	test_fraction_cross_multiply_transitivity
			-- SIMPLE_FRACTION.is_less cross-multiply comparator is a sound total order.
		local
			smt: SIMPLE_SMT
			a, c, e, two, three, four: SMT_EXPR
		do
			create smt.make
			a := smt.int_const ("a"); c := smt.int_const ("c"); e := smt.int_const ("e")
			two := smt.int_value (2); three := smt.int_value (3); four := smt.int_value (4)
			assert ("a/2<c/3 and c/3<e/4 -> a/2<e/4",
				smt.prove (three.times (a).less (two.times (c)).conjoined (four.times (c).less (three.times (e)))
					.entails (four.times (a).less (two.times (e)))))
		end

	test_decimal_split_remainder_sum_identity
			-- SIMPLE_DECIMAL.split cent distribution always reconstructs the total.
		local
			smt: SIMPLE_SMT
			total, n, td, tm, one, zero: SMT_EXPR
		do
			create smt.make
			total := smt.int_const ("total"); n := smt.int_const ("n")
			one := smt.int_value (1); zero := smt.int_value (0)
			td := total.divided_by (n)
			tm := total.modulo (n)
			assert ("r*(base+1) + (n-r)*base = total",
				smt.prove (total.at_least (zero).conjoined (n.greater (zero))
					.entails (tm.times (td.plus (one)).plus (n.minus (tm).times (td)).is_equal_to (total))))
		end

	test_fraction_negate_sign_xor
			-- SIMPLE_FRACTION.negate sign_flipped postcondition (unary_minus + xor).
		local
			smt: SIMPLE_SMT
			n, zero: SMT_EXPR
		do
			create smt.make
			n := smt.int_const ("n"); zero := smt.int_value (0)
			assert ("(-n<0 xor n<0) or n=0",
				smt.prove (n.opposite.less (zero).xored (n.less (zero)).disjoined (n.is_equal_to (zero))))
		end

feature -- Data-structure libraries

	test_slice_index_safety
			-- Slice/subarray index stays in [lower,upper] under the make preconditions.
		local
			smt: SIMPLE_SMT
			lower, upper, st, en, i, one, idx: SMT_EXPR
		do
			create smt.make
			lower := smt.int_const ("lower"); upper := smt.int_const ("upper")
			st := smt.int_const ("st"); en := smt.int_const ("en"); i := smt.int_const ("i")
			one := smt.int_value (1)
			idx := st.plus (i).minus (one)
			assert ("valid slice index in bounds",
				smt.prove (
					st.at_least (lower).conjoined (en.at_most (upper))
					  .conjoined (st.at_most (en.plus (one)))
					  .conjoined (i.at_least (one))
					  .conjoined (i.at_most (en.minus (st).plus (one)))
					.entails (lower.at_most (idx).conjoined (idx.at_most (upper)))))
		end

	test_cache_capacity_preserved_via_ite
			-- simple_cache: insert (with optional single LRU eviction) keeps count<=max.
		local
			smt: SIMPLE_SMT
			mx, cnt, one, evicted: SMT_EXPR
		do
			create smt.make
			mx := smt.int_const ("mx"); cnt := smt.int_const ("cnt"); one := smt.int_value (1)
			evicted := smt.ite (cnt.at_least (mx), cnt.minus (one), cnt)
			assert ("count stays <= max after insert",
				smt.prove (mx.greater (smt.int_value (0)).conjoined (cnt.at_most (mx))
					.entails (evicted.plus (one).at_most (mx))))
		end

	test_graph_handshake_even_lemma
			-- simple_graph edge_count: even adjacency total divides cleanly by 2.
		local
			smt: SIMPLE_SMT
			lc, two, zero: SMT_EXPR
		do
			create smt.make
			lc := smt.int_const ("lc"); two := smt.int_value (2); zero := smt.int_value (0)
			assert ("even l_count -> (l_count div 2)*2 = l_count",
				smt.prove (lc.at_least (zero).conjoined (lc.modulo (two).is_equal_to (zero))
					.entails (lc.divided_by (two).times (two).is_equal_to (lc))))
		end

	test_graph_handshake_selfloop_violation
			-- A self-loop makes l_count odd, so edge_count's integer /2 loses it (real bug shape).
		local
			smt: SIMPLE_SMT
			lc, two, zero, one: SMT_EXPR
		do
			create smt.make
			lc := smt.int_const ("lc"); two := smt.int_value (2); zero := smt.int_value (0); one := smt.int_value (1)
			smt.assume (lc.at_least (zero))
			smt.assume (lc.modulo (two).is_equal_to (one))
			smt.assume (lc.divided_by (two).times (two).is_equal_to (lc).negated)
			assert ("odd l_count witnesses the self-loop truncation", smt.is_satisfiable)
		end

	test_sorter_is_sorted_alone_is_vacuous
			-- NON-VACUITY: is_sorted without permutation admits (0,0,0) for input {1,2,3}.
		local
			smt: SIMPLE_SMT
			b1, b2, b3: SMT_EXPR
		do
			create smt.make
			b1 := smt.int_const ("b1"); b2 := smt.int_const ("b2"); b3 := smt.int_const ("b3")
			smt.assume (b1.at_most (b2))
			smt.assume (b2.at_most (b3))
			smt.assume (is_permutation_123 (smt, b1, b2, b3).negated)
			assert ("sorted-but-not-permutation is satisfiable", smt.is_satisfiable)
		end

	test_sorter_full_spec_pins_permutation
			-- With is_sorted AND permutation, (1,2,3) is the unique answer.
		local
			smt: SIMPLE_SMT
			b1, b2, b3: SMT_EXPR
		do
			create smt.make
			b1 := smt.int_const ("b1"); b2 := smt.int_const ("b2"); b3 := smt.int_const ("b3")
			assert ("sorted + permutation -> (1,2,3)",
				smt.prove (b1.at_most (b2).conjoined (b2.at_most (b3)).conjoined (is_permutation_123 (smt, b1, b2, b3))
					.entails (b1.is_equal_to (smt.int_value (1))
						.conjoined (b2.is_equal_to (smt.int_value (2)))
						.conjoined (b3.is_equal_to (smt.int_value (3))))))
		end

	test_json_array_valid_index_excludes_boundaries
			-- simple_json array: valid index 1..count excludes 0 and count+1.
		local
			smt: SIMPLE_SMT
			count, i, zero, one: SMT_EXPR
		do
			create smt.make
			count := smt.int_const ("count"); i := smt.int_const ("i")
			zero := smt.int_value (0); one := smt.int_value (1)
			assert ("valid index avoids boundary indices",
				smt.prove (count.at_least (zero).conjoined (i.at_least (one)).conjoined (i.at_most (count))
					.entails (i.is_equal_to (zero).negated.conjoined (i.is_equal_to (count.plus (one)).negated))))
		end

	test_container_chunked_ceiling_division
			-- Ceiling-division chunk count exactly covers n items with size-s chunks.
		local
			smt: SIMPLE_SMT
			n, s, one, zero, q: SMT_EXPR
		do
			create smt.make
			n := smt.int_const ("n"); s := smt.int_const ("s"); one := smt.int_value (1); zero := smt.int_value (0)
			q := n.plus (s).minus (one).divided_by (s)
			assert ("(q-1)*s < n <= q*s",
				smt.prove (n.at_least (zero).conjoined (s.greater (zero))
					.entails (q.times (s).at_least (n).conjoined (q.minus (one).times (s).less (n)))))
		end

feature -- Systems / format libraries

	test_base64_encoded_length_multiple_of_four
			-- simple_base64: encoded length is always a multiple of 4.
		local
			smt: SIMPLE_SMT
			n, k, four: SMT_EXPR
		do
			create smt.make
			n := smt.int_const ("n"); four := smt.int_value (4)
			k := n.plus (smt.int_value (2)).divided_by (smt.int_value (3))
			assert ("((n+2)/3)*4 mod 4 = 0",
				smt.prove (n.at_least (smt.int_value (0))
					.entails (k.times (four).modulo (four).is_equal_to (smt.int_value (0)))))
		end

	test_base64_length_roundtrip
			-- simple_base64: decoded length reconstructs the input byte count (ite/div/mod).
		local
			smt: SIMPLE_SMT
			n, r, g, p, zero, one, two, three: SMT_EXPR
		do
			create smt.make
			n := smt.int_const ("n")
			zero := smt.int_value (0); one := smt.int_value (1); two := smt.int_value (2); three := smt.int_value (3)
			r := n.modulo (three)
			g := n.plus (two).divided_by (three)
			p := smt.ite (r.is_equal_to (zero), zero, smt.ite (r.is_equal_to (one), two, one))
			assert ("g*3 - padding = n",
				smt.prove (n.at_least (zero).entails (g.times (three).minus (p).is_equal_to (n))))
		end

	test_iso_day_of_week_equivalence
			-- simple_datetime: two day-of-week encodings agree and stay in [1,7].
		local
			smt: SIMPLE_SMT
			d, one, seven, r_ite, r_mod: SMT_EXPR
		do
			create smt.make
			d := smt.int_const ("d"); one := smt.int_value (1); seven := smt.int_value (7)
			r_ite := smt.ite (d.minus (one).is_equal_to (smt.int_value (0)), seven, d.minus (one))
			r_mod := d.plus (smt.int_value (5)).modulo (seven).plus (one)
			assert ("ite and mod day-of-week agree in [1,7]",
				smt.prove (d.at_least (one).conjoined (d.at_most (seven))
					.entails (r_ite.is_equal_to (r_mod).conjoined (r_ite.at_least (one)).conjoined (r_ite.at_most (seven)))))
		end

	test_seconds_since_midnight_decomposition
			-- simple_datetime: h:m:s decomposition of seconds is exact and in range.
		local
			smt: SIMPLE_SMT
			s, h, m, sec: SMT_EXPR
		do
			create smt.make
			s := smt.int_const ("s")
			h := s.divided_by (smt.int_value (3600))
			m := s.modulo (smt.int_value (3600)).divided_by (smt.int_value (60))
			sec := s.modulo (smt.int_value (60))
			assert ("h*3600+m*60+sec = s and all in range",
				smt.prove (s.at_least (smt.int_value (0)).conjoined (s.less (smt.int_value (86400)))
					.entails (
						h.at_least (smt.int_value (0)).conjoined (h.at_most (smt.int_value (23)))
						.conjoined (m.at_least (smt.int_value (0))).conjoined (m.at_most (smt.int_value (59)))
						.conjoined (sec.at_least (smt.int_value (0))).conjoined (sec.at_most (smt.int_value (59)))
						.conjoined (h.times (smt.int_value (3600)).plus (m.times (smt.int_value (60))).plus (sec).is_equal_to (s)))))
		end

	test_hour_12_wraparound_range
			-- simple_datetime: 24h -> 12h clock stays in [1,12] (mod + ite midnight/noon fix).
		local
			smt: SIMPLE_SMT
			h, r, r2, twelve: SMT_EXPR
		do
			create smt.make
			h := smt.int_const ("h"); twelve := smt.int_value (12)
			r := h.modulo (twelve)
			r2 := smt.ite (r.is_equal_to (smt.int_value (0)), twelve, r)
			assert ("12h clock in [1,12]",
				smt.prove (h.at_least (smt.int_value (0)).conjoined (h.at_most (smt.int_value (23)))
					.entails (r2.at_least (smt.int_value (1)).conjoined (r2.at_most (twelve)))))
		end

	test_adler32_running_sums_bounded
			-- simple_compression adler32: running sums stay in [0,65520] under mod 65521.
		local
			smt: SIMPLE_SMT
			a, b, byte, a2, b2, m, hi: SMT_EXPR
		do
			create smt.make
			a := smt.int_const ("a"); b := smt.int_const ("b"); byte := smt.int_const ("byte")
			m := smt.int_value (65521); hi := smt.int_value (65520)
			a2 := a.plus (byte).modulo (m)
			b2 := b.plus (a2).modulo (m)
			assert ("adler running sums stay in [0,65520]",
				smt.prove (
					a.at_least (smt.int_value (0)).conjoined (a.at_most (hi))
					.conjoined (b.at_least (smt.int_value (0))).conjoined (b.at_most (hi))
					.conjoined (byte.at_least (smt.int_value (0))).conjoined (byte.at_most (smt.int_value (255)))
					.entails (
						a2.at_least (smt.int_value (0)).conjoined (a2.at_most (hi))
						.conjoined (b2.at_least (smt.int_value (0))).conjoined (b2.at_most (hi)))))
		end

	test_base64_weak_length_spec_admits_stub
			-- NON-VACUITY: result_count>=0 admits a stub encoder returning 0 for 5 bytes.
		local
			smt: SIMPLE_SMT
			rc, expected: SMT_EXPR
		do
			create smt.make
			rc := smt.int_const ("rc")
			expected := smt.int_value (5).plus (smt.int_value (2)).divided_by (smt.int_value (3)).times (smt.int_value (4))
			smt.assume (rc.is_equal_to (smt.int_value (0)))
			smt.assume (rc.at_least (smt.int_value (0)))
			smt.assume (rc.is_equal_to (expected).negated)
			assert ("weak length spec satisfied by stub (rc=0)", smt.is_satisfiable)
		end

	test_base64_strong_length_spec_pins_value
			-- The real postcondition forces result_count = 8 for 5 input bytes.
		local
			smt: SIMPLE_SMT
			rc, expected: SMT_EXPR
		do
			create smt.make
			rc := smt.int_const ("rc")
			expected := smt.int_value (5).plus (smt.int_value (2)).divided_by (smt.int_value (3)).times (smt.int_value (4))
			smt.assume (rc.is_equal_to (expected))
			smt.assume (rc.is_equal_to (smt.int_value (8)).negated)
			assert ("strong spec pins rc=8 (no other value)", smt.is_unsatisfiable)
		end

feature -- Classic verification problems

	test_pigeonhole_3_into_2
			-- 3 pairwise-distinct values cannot fit in {0,1}.
		do
			assert ("pigeonhole 3->2 unsat", pigeonhole_unsat (3, 0, 1))
		end

	test_pigeonhole_5_into_4
			-- 5 pairwise-distinct values cannot fit in {1..4}.
		do
			assert ("pigeonhole 5->4 unsat", pigeonhole_unsat (5, 1, 4))
		end

	test_triangle_3coloring_sat
			-- K3 is 3-colorable.
		do
			assert ("triangle 3-coloring sat", coloring_sat (3, 3))
		end

	test_k4_3coloring_unsat
			-- K4 needs 4 colors; 3 is impossible.
		do
			assert ("K4 3-coloring unsat", not coloring_sat (4, 3))
		end

	test_latin_square_row_sat
			-- A 4-cell row with values 1..4 all distinct is satisfiable.
		do
			assert ("latin row 4 sat", coloring_sat (4, 4))
		end

	test_array_bounds_loop_invariant
			-- The index invariant is preserved by i := i+1 under the loop guard.
		local
			smt: SIMPLE_SMT
			i, n, zero, one: SMT_EXPR
		do
			create smt.make
			i := smt.int_const ("i"); n := smt.int_const ("n"); zero := smt.int_value (0); one := smt.int_value (1)
			assert ("(0<=i<=n and i<n) -> 0<=i+1<=n",
				smt.prove (zero.at_most (i).conjoined (i.at_most (n)).conjoined (i.less (n))
					.entails (zero.at_most (i.plus (one)).conjoined (i.plus (one).at_most (n)))))
		end

	test_integer_overflow_bound
			-- Sum of two bounded values respects the composed bound (no wraparound).
		local
			smt: SIMPLE_SMT
			a, b, k, k2: SMT_EXPR
		do
			create smt.make
			a := smt.int_const ("a"); b := smt.int_const ("b")
			k := smt.int_value (1000); k2 := smt.int_value (2000)
			assert ("a<=1000 and b<=1000 -> a+b<=2000",
				smt.prove (a.at_most (k).conjoined (b.at_most (k)).entails (a.plus (b).at_most (k2))))
		end

	test_max_via_ite_correct
			-- ite-defined maximum satisfies the max postcondition.
		local
			smt: SIMPLE_SMT
			a, b, m: SMT_EXPR
		do
			create smt.make
			a := smt.int_const ("a"); b := smt.int_const ("b")
			m := smt.maximum (a, b)
			assert ("max: m>=a and m>=b and (m=a or m=b)",
				smt.prove (m.at_least (a).conjoined (m.at_least (b)).conjoined (m.is_equal_to (a).disjoined (m.is_equal_to (b)))))
		end

	test_abs_via_ite_correct
			-- ite-defined absolute value satisfies the abs postcondition.
		local
			smt: SIMPLE_SMT
			x, ax: SMT_EXPR
		do
			create smt.make
			x := smt.int_const ("x")
			ax := smt.absolute (x)
			assert ("abs: ax>=0 and (ax=x or ax=-x)",
				smt.prove (ax.at_least (smt.int_value (0)).conjoined (ax.is_equal_to (x).disjoined (ax.is_equal_to (x.opposite)))))
		end

	test_day_of_week_modular_period
			-- Adding a full week never changes the day-of-week residue.
		local
			smt: SIMPLE_SMT
			d, seven: SMT_EXPR
		do
			create smt.make
			d := smt.int_const ("d"); seven := smt.int_value (7)
			assert ("(d+7) mod 7 = d mod 7",
				smt.prove (d.plus (seven).modulo (seven).is_equal_to (d.modulo (seven))))
		end

	test_nonlinear_sqrt2_unsat_over_ints
			-- KNOWN CAPABILITY: x*x=2 has no integer solution (Z3 decides).
		local
			smt: SIMPLE_SMT
			x: SMT_EXPR
		do
			create smt.make
			x := smt.int_const ("x")
			smt.assume (x.times (x).is_equal_to (smt.int_value (2)))
			assert ("x*x=2 unsat over integers", smt.is_unsatisfiable)
		end

	test_nonlinear_sqrt2_sat_over_reals
			-- KNOWN CAPABILITY: x*x=2 IS solvable over the reals.
		local
			smt: SIMPLE_SMT
			x: SMT_EXPR
		do
			create smt.make
			x := smt.real_const ("x")
			smt.assume (x.times (x).is_equal_to (smt.real_value ("2")))
			assert ("x*x=2 sat over reals", smt.is_satisfiable)
		end

feature -- AutoProof ACCOUNT reproduction (comcom.csail.mit.edu)

	test_account_withdraw_invariant_bug
			-- REPRODUCE AutoProof: without amount<=balance, withdraw can break balance>=0.
		local
			smt: SIMPLE_SMT
			bal, amt, zero: SMT_EXPR
		do
			create smt.make
			bal := smt.int_const ("balance"); amt := smt.int_const ("amount"); zero := smt.int_value (0)
				-- VC: (balance>=0 and amount>=0 and balance' = balance-amount) => balance'>=0  -- NOT valid.
			assert ("withdraw invariant NOT provable (matches AutoProof red)",
				not smt.prove (bal.at_least (zero).conjoined (amt.at_least (zero))
					.entails (bal.minus (amt).at_least (zero))))
			assert ("counter-model exists",
				not smt.refutation (bal.at_least (zero).conjoined (amt.at_least (zero))
					.entails (bal.minus (amt).at_least (zero))).is_empty)
		end

	test_account_withdraw_decreased_bug
			-- REPRODUCE AutoProof: balance_decreased fails when amount=0.
		local
			smt: SIMPLE_SMT
			bal, amt, zero: SMT_EXPR
		do
			create smt.make
			bal := smt.int_const ("balance"); amt := smt.int_const ("amount"); zero := smt.int_value (0)
				-- VC: (amount>=0 and balance'=balance-amount) => balance' < balance  -- NOT valid (amount=0).
			assert ("withdraw balance_decreased NOT provable (matches AutoProof red)",
				not smt.prove (amt.at_least (zero).entails (bal.minus (amt).less (bal))))
		end

	test_account_transfer_decreased_bug
			-- REPRODUCE AutoProof: transfer's balance_decreased has the same amount=0 hole.
		local
			smt: SIMPLE_SMT
			bal, amt, zero: SMT_EXPR
		do
			create smt.make
			bal := smt.int_const ("balance"); amt := smt.int_const ("amount"); zero := smt.int_value (0)
			assert ("transfer balance_decreased NOT provable (matches AutoProof red)",
				not smt.prove (amt.at_least (zero).entails (bal.minus (amt).less (bal))))
		end

	test_account_withdraw_invariant_fixed
			-- THE FIX: add precondition amount<=balance -> invariant now provable.
		local
			smt: SIMPLE_SMT
			bal, amt, zero: SMT_EXPR
		do
			create smt.make
			bal := smt.int_const ("balance"); amt := smt.int_const ("amount"); zero := smt.int_value (0)
			assert ("with amount<=balance, invariant IS provable",
				smt.prove (bal.at_least (zero).conjoined (amt.at_least (zero)).conjoined (amt.at_most (bal))
					.entails (bal.minus (amt).at_least (zero))))
		end

	test_account_withdraw_decreased_fixed
			-- THE FIX: strengthen precondition to amount>0 -> balance_decreased provable.
		local
			smt: SIMPLE_SMT
			bal, amt, zero: SMT_EXPR
		do
			create smt.make
			bal := smt.int_const ("balance"); amt := smt.int_const ("amount"); zero := smt.int_value (0)
			assert ("with amount>0, balance_decreased IS provable",
				smt.prove (amt.greater (zero).entails (bal.minus (amt).less (bal))))
		end

feature {NONE} -- Helpers

	is_permutation_123 (a_smt: SIMPLE_SMT; b1, b2, b3: SMT_EXPR): SMT_EXPR
			-- Encodes "b1,b2,b3 is a permutation of {1,2,3}": distinct and each in [1,3].
		local
			one, three: SMT_EXPR
		do
			one := a_smt.int_value (1); three := a_smt.int_value (3)
			Result := a_smt.all_distinct (<<b1, b2, b3>>)
				.conjoined (one.at_most (b1)).conjoined (b1.at_most (three))
				.conjoined (one.at_most (b2)).conjoined (b2.at_most (three))
				.conjoined (one.at_most (b3)).conjoined (b3.at_most (three))
		end

	pigeonhole_unsat (a_pigeons, a_lo, a_hi: INTEGER): BOOLEAN
			-- Is placing `a_pigeons' pairwise-distinct values into [a_lo,a_hi] unsatisfiable?
		require
			at_least_two: a_pigeons >= 2
		local
			smt: SIMPLE_SMT
			l_vars: ARRAYED_LIST [SMT_EXPR]
			i: INTEGER
			v: SMT_EXPR
		do
			create smt.make
			create l_vars.make (a_pigeons)
			from i := 1 until i > a_pigeons loop
				v := smt.int_const ("p" + i.out)
				smt.assume (v.at_least (smt.int_value (a_lo)))
				smt.assume (v.at_most (smt.int_value (a_hi)))
				l_vars.extend (v)
				i := i + 1
			end
			smt.assume (smt.all_distinct (l_vars.to_array))
			Result := smt.is_unsatisfiable
		end

	coloring_sat (a_nodes, a_colors: INTEGER): BOOLEAN
			-- Is a complete graph on `a_nodes' nodes properly colorable with `a_colors' colors?
			-- (all nodes mutually adjacent -> all colors must differ.)
		require
			at_least_two: a_nodes >= 2
		local
			smt: SIMPLE_SMT
			l_vars: ARRAYED_LIST [SMT_EXPR]
			i: INTEGER
			v: SMT_EXPR
		do
			create smt.make
			create l_vars.make (a_nodes)
			from i := 1 until i > a_nodes loop
				v := smt.int_const ("c" + i.out)
				smt.assume (v.at_least (smt.int_value (1)))
				smt.assume (v.at_most (smt.int_value (a_colors)))
				l_vars.extend (v)
				i := i + 1
			end
			smt.assume (smt.all_distinct (l_vars.to_array))
			Result := smt.is_satisfiable
		end

end
