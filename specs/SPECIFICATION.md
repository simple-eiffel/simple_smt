# simple_smt — Specification v1.0 (Phase 0)

**A native Eiffel binding to the Z3 SMT solver's C API.**
The durable substrate for the Auto-spec / correctness tooling arc.

**Date:** 2026-07-18 · Z3 5.0.0 (MIT), vendored.

## 1. Mission

Give Eiffel programs first-class access to an SMT solver: build logical formulas
over integers, reals, and booleans; assert them; and decide satisfiability, extract
models, and — the headline convenience — **prove** a conjecture (assert its negation,
check for `unsat`). 100% Eiffel facade over Z3's C API via inline-C externals
(Z3 is the allowed "C-lib looped in"). No Boogie, no external process, no proprietary
dependency.

**Non-goals (Phase 0):** quantifiers, arrays/bitvectors/strings theories, optimization,
tactics, proof objects, incremental unsat cores. (Extensible later; the binding layer
is designed so adding a sort/op is one external + one facade feature.)

## 2. Architecture

```
SMT_Z3_API        -- all inline-C externals over <z3.h>; stateless, ctx passed in
SMT_CONTEXT       -- owns Z3_config + Z3_context; sort cache; expression factories
SMT_EXPR          -- wraps a Z3_ast + its context; fluent operators
SMT_SOLVER        -- wraps Z3_solver (ref-counted); assert/check/push/pop/model/smtlib
SMT_MODEL         -- wraps Z3_model; value_of(expr) -> STRING
SIMPLE_SMT        -- facade: context+solver together; is_satisfiable / prove / model_value
```

Z3 handles are opaque pointers held as `POINTER`. Contexts use `Z3_mk_context`
(AST lifetime tied to the context — no per-AST ref counting needed); only solver and
model carry `inc_ref`/`dec_ref`.

## 3. Core API (facade `SIMPLE_SMT`)

```eiffel
create smt.make

x := smt.int_const ("x")
one := smt.int_value (1)
zero := smt.int_value (0)

-- Prove:  x >= 0  implies  x + 1 > 0
conjecture := x.at_least (zero).implies (x.plus (one).greater (zero))
if smt.prove (conjecture) then print ("THEOREM%N") end     -- True: Z3 finds negation unsat

-- Satisfy:  x > 5 and x < 8
smt.assume (x.greater (smt.int_value (5)))
smt.assume (x.less (smt.int_value (8)))
if smt.is_satisfiable then print (smt.model_value (x)) end  -- e.g. "6" or "7"
```

**Facade features:**
- Builders: `int_const/real_const/bool_const (name)`, `int_value (i)`, `real_value (s)`,
  `true_expr`, `false_expr`.
- `assume (e)` — add `e` to the solver's assertion set.
- `is_satisfiable: BOOLEAN` / `is_unsatisfiable` / `is_unknown` — run the check.
- `prove (conjecture): BOOLEAN` — push, assert `not conjecture`, check `unsat`, pop.
  True iff the conjecture is valid (holds for all values). Never mutates the assertion set.
- `model_value (e): STRING` — value of `e` in the last satisfying model ("" if none).
- `push` / `pop` / `reset`.
- `to_smtlib: STRING` — the SMT-LIB2 text of current assertions.

**`SMT_EXPR` fluent ops** (each returns a new SMT_EXPR): `plus/minus/times`,
`less/at_most/greater/at_least/is_equal_to` (arith comparisons), `implies`,
`conjoined/disjoined` (bool), `negated`, `to_string`.

## 4. Guarantees / contracts

- Every builder requires a non-empty name / valid arg and ensures an attached expr
  whose `context` is this context.
- `prove` leaves the assertion set unchanged (push/pop bracketed) — postcondition
  `assertion_count = old assertion_count`.
- `SMT_SOLVER` invariant: `solver /= default_pointer`.
- Void-safe; SCOOP-compatible types.

## 5. Determinism & correctness claim

Z3 is the trusted oracle. simple_smt's own claim is only faithful *translation*:
the Eiffel expression tree maps 1:1 to Z3 AST nodes. This is validated by the test
suite proving known theorems (`unsat` of their negations) and refuting known
non-theorems (`sat` with an extracted counter-model) — differential grounding, the
same discipline as `simple_compression.crc32`'s `agrees_with_reference`.

## 6. Test plan (≥16)

Sat/unsat basics; model extraction; arithmetic identities proven
(`x+0=x`, `x+1>x`, transitivity `x<y and y<z -> x<z`); boolean tautologies
(`a or not a`, De Morgan); contradiction detection (`x>0 and x<0 -> unsat`);
the contract-fragment discharge from the theory turns (`x>=0 -> x+1>0`,
`1<=k and k<=n -> k<=n`); `prove` non-mutation; push/pop scoping; reset;
counter-model for a false conjecture; SMT-LIB emission; real arithmetic
(`2*x=1 -> x=1/2` sat over reals, unsat over ints).

## 7. Build

Z3 vendored: `Clib/z3.h` (+deps), `lib/libz3.lib`, `lib/libz3.dll` (copied beside
the exe at runtime). ECF wires `external_include` (Clib) + `external_object`
(libz3.lib). Targets: library, `_tests`, `_app`.
