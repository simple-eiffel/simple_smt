# simple_smt

[Documentation](https://simple-eiffel.github.io/simple_smt/) •
[GitHub](https://github.com/simple-eiffel/simple_smt) •
[Issues](https://github.com/simple-eiffel/simple_smt/issues)

![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)
![Eiffel 25.02](https://img.shields.io/badge/Eiffel-25.02-purple.svg)
![DBC: Contracts](https://img.shields.io/badge/DBC-Contracts-green.svg)
![Windows: tests pass](https://img.shields.io/badge/Windows-tests%20pass-0078D6?logo=windows&logoColor=white) ![Linux: tests pass](https://img.shields.io/badge/Linux-tests%20pass-FCC624?logo=linux&logoColor=black) ![macOS: tests pass](https://img.shields.io/badge/macOS-tests%20pass-000000?logo=apple&logoColor=white)

A native Eiffel binding to the [Z3](https://github.com/Z3Prover/z3) SMT solver — build logical
formulas over integers, reals, and booleans; decide satisfiability; extract models; and **prove**
theorems, all from Eiffel.

Part of the [Simple Eiffel](https://github.com/simple-eiffel) ecosystem.

## Status

✅ v1.0.0 — **56 tests passing (100%)**, including 35 real-world scenarios mined from actual
simple_* contracts and a reproduction of the MIT AutoProof ACCOUNT tutorial. Z3 5.0.0 (MIT)
vendored; inline-C binding over `z3.h`. Cross-platform by construction (Windows tested).

For complete documentation, see [our docs site](https://simple-eiffel.github.io/simple_smt/).

## Quick Start

```eiffel
local
    smt: SIMPLE_SMT
    x, zero, one: SMT_EXPR
do
    create smt.make
    x := smt.int_const ("x")
    zero := smt.int_value (0)
    one := smt.int_value (1)

    -- Prove a theorem (valid for all x):  x >= 0  implies  x + 1 > 0
    if smt.prove (x.at_least (zero).entails (x.plus (one).greater (zero))) then
        print ("PROVED%N")
    end

    -- Refute a non-theorem with a counter-model
    print (smt.refutation (x.greater (zero)))     -- witness where x > 0 is false

    -- Solve a constraint and read the model
    smt.assume (x.greater (smt.int_value (5)))
    smt.assume (x.less (smt.int_value (8)))
    if smt.is_satisfiable then print (smt.model_value (x)) end   -- 6 or 7
end
```

## API

**`SIMPLE_SMT` facade**
- Builders: `int_const/real_const/bool_const (name)`, `int_value (i)`, `real_value (s)`, `true_expr`, `false_expr`
- `assume (e)` — add a formula to the assertion set
- `is_satisfiable` / `is_unsatisfiable` / `is_unknown`
- `prove (conjecture): BOOLEAN` — valid for all values? (asserts the negation, checks `unsat`; never mutates the assertion set)
- `refutation (conjecture): STRING` — counter-model if not valid, else ""
- `model_value (e): STRING` — value of `e` in the current model
- `push` / `pop` / `reset` / `to_smtlib`

**`SMT_EXPR` fluent operators** (each returns a new expression)
- Arithmetic: `plus`, `minus`, `times`
- Comparison: `less`, `at_most`, `greater`, `at_least`, `is_equal_to`
- Boolean: `conjoined` (and), `disjoined` (or), `entails` (implies), `negated` (not)

> Note: `entails` and `decide` are named to avoid the Eiffel keywords `implies` and `check`.

## Why

`simple_smt` is the mechanical core — the "dispose" in propose/dispose — under contract
verification, non-vacuity checking, and spec synthesis. Z3 is the trusted oracle; this
library's only claim is faithful translation of the Eiffel expression tree into Z3's AST,
grounded by a suite that proves known theorems and refutes known non-theorems.

## Installation

```
<library name="simple_smt" location="$SIMPLE_EIFFEL/simple_smt/simple_smt.ecf"/>
```

Z3 is vendored (`Clib/z3.h`, `lib/libz3.lib`); `libz3.dll` must sit beside the executable
at runtime (the build copies it into `bin/`).

```bash
/d/prod/ec.sh test -config simple_smt.ecf -target simple_smt_tests   # 17/17
./bin/test_app.exe
```

## Scope (v1.0)

Integers, reals, booleans; arithmetic, comparison, boolean connectives; assert/check/model/
push/pop; SMT-LIB emission. Not yet: quantifiers, arrays/bitvectors/strings theories,
optimization, proof objects — the binding is designed so each is one external + one facade feature.

## License

MIT. Bundled Z3 is MIT (see `lib/Z3_LICENSE.txt`).
