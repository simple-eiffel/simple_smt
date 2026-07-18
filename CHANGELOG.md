# Changelog

## 1.0.0 — 2026-07-18

Initial release. Native Eiffel binding to the Z3 SMT solver.

### Added
- `SIMPLE_SMT` facade: build formulas over integers, reals, booleans; `assume`,
  `is_satisfiable`/`is_unsatisfiable`, `prove` (validity via negation-unsat, non-mutating),
  `refutation` (counter-model), `model_value`, `push`/`pop`/`reset`, `to_smtlib`.
- `SMT_EXPR` fluent operators: `plus/minus/times`, `less/at_most/greater/at_least/is_equal_to`,
  `conjoined/disjoined/entails/negated`.
- `SMT_CONTEXT` (Z3 config/context + inline-C externals over `z3.h`), `SMT_SOLVER`, `SMT_MODEL`.
- Z3 5.0.0 (MIT) vendored: `Clib/z3.h` (+deps), `lib/libz3.lib`, `lib/libz3.dll`.
- 17 tests: sat/unsat, model extraction, proven theorems (`x>=0 -> x+1>0`, transitivity,
  De Morgan, `1<=k<=n -> k<=n`), refutation with counter-models, reals-vs-ints, prove
  non-mutation, push/pop scoping, SMT-LIB emission. Demo app.

### Notes
- `entails` / `decide` are named to avoid the Eiffel keywords `implies` / `check`.
- Z3 is the trusted oracle; the library's claim is faithful Eiffel→Z3-AST translation,
  grounded by the theorem/refutation suite.
- Phase 0 of the AutoSpec correctness tooling: the mechanical core under contract
  verification, non-vacuity checking, and spec synthesis.
