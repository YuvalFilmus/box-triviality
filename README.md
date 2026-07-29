# Box-triviality in Lean

[![Lean build](https://github.com/YuvalFilmus/box-triviality/actions/workflows/lean.yml/badge.svg)](https://github.com/YuvalFilmus/box-triviality/actions/workflows/lean.yml)

A Lean 4 formalization of the results in *Triviality of promise
polymorphisms*.

## Contents

All declarations below are in the `BoxTriviality` namespace.

| Category | Item | Lean declarations | File |
| --- | --- | --- | --- |
| Definitions | Multisorted tuples, relations, operations, and promise polymorphisms | `Tuple`, `Relation`, `Operation`, `applyOperation`, `Preserves` | [`Defs.lean`](BoxTriviality/Defs.lean) |
| Definitions | Dictator and box types | `IsDictator`, `InImageBox`, `IsBox`, `IsBoxTrivial` | [`Defs.lean`](BoxTriviality/Defs.lean) |
| Definitions | Box-triviality at one arity and at all positive arities | `BoxTrivialAtArity`, `BoxTrivialAtAllArities` | [`Defs.lean`](BoxTriviality/Defs.lean) |
| Definitions | Certificate type and certificate-triviality | `IsCertificate`, `IsCertificateTrivial`, `CertificateTrivialAtArity`, `CertificateTrivialAtAllArities` | [`Defs.lean`](BoxTriviality/Defs.lean) |
| Definitions | Full projections, permutation families, and synchronicity | `HasFullProjections`, `IsPermutationFamily`, `IsSynchronous` | [`Defs.lean`](BoxTriviality/Defs.lean) |
| Definitions | Alphabet-size conditions and the two obstructions | `HasAtLeastTwo`, `HasExactlyTwo`, `HasUnitWitness`, `HasGeneralizedUpset` | [`Defs.lean`](BoxTriviality/Defs.lean) |
| Theorem 1.3 | Reduction of box-triviality to binary arity | `boxTrivialAtAllArities_iff_binary` | [`ReductionToBinary.lean`](BoxTriviality/ReductionToBinary.lean) |
| Corollary 3.3 | Reduction of certificate-triviality to binary arity | `certificateTrivialAtAllArities_iff_binary` | [`ReductionToBinary.lean`](BoxTriviality/ReductionToBinary.lean) |
| Theorem 1.4 | Reduction of box-triviality to unary arity, subject to the absence of the two obstructions | `boxTrivialAtAllArities_iff_unary_no_obstructions` | [`ReductionToUnary.lean`](BoxTriviality/ReductionToUnary.lean) |
| First example | Box-triviality in every positive arity, but not certificate-triviality in unary arity | `BoxNotCertificate.boxTrivialAtAllArities`, `BoxNotCertificate.not_certificateTrivialAtOne` | [`Examples.lean`](BoxTriviality/Examples.lean) |
| Remark example | Box-triviality in unary arity, but not in binary arity | `DifferentAlphabetsCounterexample.boxTrivialAtOne`, `DifferentAlphabetsCounterexample.not_boxTrivialAtTwo` | [`Examples.lean`](BoxTriviality/Examples.lean) |

## Building

```text
lake update
lake build
```
