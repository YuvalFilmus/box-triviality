# Box-triviality in Lean

[![Lean build](https://github.com/YuvalFilmus/box-triviality/actions/workflows/lean.yml/badge.svg)](https://github.com/YuvalFilmus/box-triviality/actions/workflows/lean.yml)

A Lean 4 formalization of the results in *Triviality of promise
polymorphisms*.

## Contents

All declarations below are in the `BoxTriviality` namespace.

The basic definitions are in [`BoxTriviality/Defs.lean`](BoxTriviality/Defs.lean).

| Category | Lean declarations | File |
| --- | --- | --- |
| Theorem 1.3 | `boxTrivialAtAllArities_iff_binary` | [`ReductionToBinary.lean`](BoxTriviality/ReductionToBinary.lean) |
| Corollary 3.3 | `certificateTrivialAtAllArities_iff_binary` | [`ReductionToBinary.lean`](BoxTriviality/ReductionToBinary.lean) |
| Theorem 1.4 | `boxTrivialAtAllArities_iff_unary_no_obstructions` | [`ReductionToUnary.lean`](BoxTriviality/ReductionToUnary.lean) |
| First example | `BoxNotCertificate.boxTrivialAtAllArities`, `BoxNotCertificate.not_certificateTrivialAtOne` | [`Examples.lean`](BoxTriviality/Examples.lean) |
| Remark example | `DifferentAlphabetsCounterexample.boxTrivialAtOne`, `DifferentAlphabetsCounterexample.not_boxTrivialAtTwo` | [`Examples.lean`](BoxTriviality/Examples.lean) |

## Building

```text
lake update
lake build
```
