# Box-triviality in Lean

[![Lean build](https://github.com/YuvalFilmus/box-triviality/actions/workflows/lean.yml/badge.svg)](https://github.com/YuvalFilmus/box-triviality/actions/workflows/lean.yml)

A Lean 4 formalization of the results in *Triviality of promise
polymorphisms*.

The formalization is being developed in five stages:

1. foundational definitions;
2. the reduction to binary (Theorem 1.3);
3. the certificate version of the reduction to binary (Corollary 3.3);
4. the reduction to unary (Theorem 1.4);
5. the two examples from the introduction.

The alphabets are arbitrary Lean types and may be infinite. The project
depends on Mathlib, but each source file imports only the Mathlib modules it
uses; it never imports the umbrella `Mathlib` module.

The definitions currently require only `Mathlib.Data.Set.Defs`; `Fin` and the
remaining logical primitives used there are provided by Lean itself.

## Current contents

[`BoxTriviality/Defs.lean`](BoxTriviality/Defs.lean) contains the definitions
of multisorted relations and operations, promise polymorphisms, dictator,
box, and certificate types, triviality at one or all positive arities, full
projections, synchronous permutation families, and the two obstructions from
Theorem 1.4.

[`BoxTriviality/ReductionToBinary.lean`](BoxTriviality/ReductionToBinary.lean)
formalizes Theorem 1.3. Its main result is
`boxTrivialAtAllArities_iff_binary`. The same file formalizes Corollary 3.3
as `certificateTrivialAtAllArities_iff_binary`. Both proofs work for arbitrary
coordinate types and arbitrary, possibly infinite, alphabets.

[`BoxTriviality/ReductionToUnary.lean`](BoxTriviality/ReductionToUnary.lean)
formalizes Theorem 1.4 as
`boxTrivialAtAllArities_iff_unary_no_obstructions`.

[`BoxTriviality/Examples.lean`](BoxTriviality/Examples.lean) formalizes both
examples from the introduction: the relation which is box-trivial in every
positive arity but not certificate-trivial even in unary arity, and the
different-alphabet counterexample from the remark.

## Building

```text
lake update
lake build
```
