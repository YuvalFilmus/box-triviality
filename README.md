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
| First example | The relation and diagonal identity family | `BoxNotCertificate.relation`, `BoxNotCertificate.identityFamily` | [`Examples.lean`](BoxTriviality/Examples.lean) |
| First example | Box-triviality in every positive arity | `BoxNotCertificate.boxTrivialAtAllArities` | [`Examples.lean`](BoxTriviality/Examples.lean) |
| First example | Failure of certificate-triviality in unary arity | `BoxNotCertificate.nonCertificateOperation`, `BoxNotCertificate.nonCertificateOperation_preserves`, `BoxNotCertificate.nonCertificateOperation_isBox`, `BoxNotCertificate.not_certificateTrivialAtOne` | [`Examples.lean`](BoxTriviality/Examples.lean) |
| Remark example | The input relation, output relation, and injection family | `DifferentAlphabetsCounterexample.inputRelation`, `DifferentAlphabetsCounterexample.outputRelation`, `DifferentAlphabetsCounterexample.injectionFamily` | [`Examples.lean`](BoxTriviality/Examples.lean) |
| Remark example | The natural injective homomorphism | `DifferentAlphabetsCounterexample.diagonalInclusion`, `DifferentAlphabetsCounterexample.diagonalInclusion_mem`, `DifferentAlphabetsCounterexample.diagonalInclusion_polymorphism` | [`Examples.lean`](BoxTriviality/Examples.lean) |
| Remark example | Unary box-triviality | `DifferentAlphabetsCounterexample.boxTrivialAtOne` | [`Examples.lean`](BoxTriviality/Examples.lean) |
| Remark example | Binary polymorphism witnessing failure of box-triviality | `DifferentAlphabetsCounterexample.binaryOperation`, `DifferentAlphabetsCounterexample.binaryOperation_preserves`, `DifferentAlphabetsCounterexample.binaryOperation_not_boxTrivial`, `DifferentAlphabetsCounterexample.not_boxTrivialAtTwo` | [`Examples.lean`](BoxTriviality/Examples.lean) |

## Building

```text
lake update
lake build
```
