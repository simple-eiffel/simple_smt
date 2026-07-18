# Test Suite Report — simple_smt

**Date:** 2026-07-18 · **Compiler:** EiffelStudio 25.02.9.8732 · **Z3:** 5.0.0 (MIT)
**Binary:** F_code finalized `-keep` (contracts active)

## Result

```
Results: 56 passed, 0 failed
ALL TESTS PASSED
```

- 17 core tests (sat/unsat, model extraction, proven theorems, refutation, reals-vs-ints, mechanics)
- 35 real-world tests mined from the simple_* ecosystem by a fleet of research agents
- 5 AutoProof ACCOUNT reproductions

## Real-world coverage — grounded in actual ecosystem contracts

| Test | Provenance | Verdict |
|---|---|---|
| uniform_mean_between_bounds | simple_probability UNIFORM_DISTRIBUTION.mean | proved |
| binomial weak / strong | simple_probability BINOMIAL_DISTRIBUTION.make (non-vacuity pair) | sat / unsat |
| fraction_cross_multiply_transitivity | simple_fraction SIMPLE_FRACTION.is_less | proved |
| decimal_split_remainder_sum_identity | simple_decimal SIMPLE_DECIMAL.split (mod/div) | proved |
| fraction_negate_sign_xor | simple_fraction SIMPLE_FRACTION.negate (unary_minus/xor) | proved |
| slice_index_safety | subarray index bounds | proved |
| cache_capacity_preserved_via_ite | simple_cache insert+evict (ite) | proved |
| graph_handshake even / self-loop | simple_graph edge_count (mod/div) | proved / sat |
| sorter is_sorted-alone / full spec | non-vacuity: sorted vs sorted+permutation | sat / proved |
| json_array_valid_index | simple_json index invariant | proved |
| container_chunked_ceiling_division | ceiling-division chunk count (div) | proved |
| base64 length ×4 / roundtrip | simple_base64 (div/mod/ite) | proved |
| iso_day_of_week / hour_12 / seconds_hms | simple_datetime (mod/div/ite) | proved |
| adler32_running_sums_bounded | simple_compression adler32 mod 65521 | proved |
| base64 weak / strong length | non-vacuity: stub-admitting vs pinned | sat / unsat |
| pigeonhole 3→2, 5→4 | classic (distinct) | unsat |
| triangle / K4 / latin-row coloring | classic (distinct) | sat / unsat / sat |
| array_bounds_loop_invariant | loop-invariant discharge | proved |
| integer_overflow_bound | bounded-sum no wraparound | proved |
| max / abs via ite | ite correctness | proved |
| day_of_week_modular_period | (d+7) mod 7 = d mod 7 | proved |
| nonlinear sqrt2 int / real | KNOWN CAPABILITY: x*x=2 (Z3 decides both) | unsat / sat |

## AutoProof ACCOUNT reproduction (comcom.csail.mit.edu)

simple_smt independently reproduces the three failures the MIT AutoProof verifier
flags on the ACCOUNT tutorial, then proves the fixed versions:

| VC | AutoProof result | simple_smt |
|---|---|---|
| withdraw preserves `balance >= 0` (no `amount <= balance` pre) | Invariant may not hold | **refuted** (counter-model) |
| withdraw `balance_decreased` (amount=0 hole) | Postcondition may be violated | **refuted** |
| transfer `balance_decreased` | Postcondition may be violated | **refuted** |
| withdraw invariant WITH `amount <= balance` | (the fix) | **proved** |
| withdraw decreased WITH `amount > 0` | (the fix) | **proved** |

## What this demonstrates

- **Genuine program verification**, not a toy: discharges real contract-fragment VCs,
  detects under-constrained (vacuous) specs with concrete witnesses, and matches a
  research-grade verifier's output on a canonical example.
- **Operator range**: integers, reals, `+ - * mod div`, comparisons, boolean connectives,
  `xor`/`iff`/`ite`/`unary_minus`, pairwise `distinct`.
- **Honest limits**: nonlinear cases that Z3 decides are tested (`x*x=2`); deeper
  Diophantine cases (Fermat cubic, Pell) were identified by the fleet as beyond reliable
  reach and deliberately excluded rather than shipped as flaky tests.

Full log: `reports/test_run.log`.
