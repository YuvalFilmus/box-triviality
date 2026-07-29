import Mathlib.Data.Set.Defs

/-!
# Promise polymorphisms and box-triviality

This file formalizes the definitions used in *Triviality of promise
polymorphisms*. Alphabets are arbitrary types: in particular, no finiteness
assumption is made.
-/

namespace BoxTriviality

universe uι uA uB

variable {ι : Type uι}

/-- A multisorted tuple with coordinate types `A i`. -/
abbrev Tuple (A : ι → Type uA) := ∀ i, A i

/-- A multisorted relation is a set of multisorted tuples. -/
abbrev Relation (A : ι → Type uA) := Set (Tuple A)

/--
An `n`-ary multisorted operation from the alphabets `A` to the alphabets `B`.
The operation in coordinate `i` receives the `i`th column of an `n`-row input.
-/
abbrev Operation (n : Nat) (A : ι → Type uA) (B : ι → Type uB) :=
  ∀ i, (Fin n → A i) → B i

/-- A unary multisorted map from `A` to `B`. -/
abbrev UnaryMap (A : ι → Type uA) (B : ι → Type uB) :=
  ∀ i, A i → B i

/-- The output obtained by applying `f` coordinatewise to the rows `x`. -/
def applyOperation {A : ι → Type uA} {B : ι → Type uB} {n : Nat}
    (f : Operation n A B) (x : Fin n → Tuple A) : Tuple B :=
  fun i ↦ f i (fun r ↦ x r i)

/--
`f` is a polymorphism of the relation pair `(P, Q)`: whenever all input rows
belong to `P`, their coordinatewise image belongs to `Q`.
-/
def Preserves {A : ι → Type uA} {B : ι → Type uB} {n : Nat}
    (P : Relation A) (Q : Relation B) (f : Operation n A B) : Prop :=
  ∀ x : Fin n → Tuple A, (∀ r, x r ∈ P) → applyOperation f x ∈ Q

/--
The tuple `y` belongs to the Cartesian product of the coordinatewise images
of `f`.
-/
def InImageBox {A : ι → Type uA} {B : ι → Type uB} {n : Nat}
    (f : Operation n A B) (y : Tuple B) : Prop :=
  ∀ i, ∃ x : Fin n → A i, f i x = y i

/-- The Cartesian product of the coordinatewise images of `f` is contained in `Q`. -/
def IsBox {A : ι → Type uA} {B : ι → Type uB} {n : Nat}
    (Q : Relation B) (f : Operation n A B) : Prop :=
  ∀ ⦃y⦄, InImageBox f y → y ∈ Q

/--
`f` is of dictator type with respect to `Φ`: every coordinate applies the
corresponding component of one member of `Φ` to the same input row.
-/
def IsDictator {A : ι → Type uA} {B : ι → Type uB} {n : Nat}
    (Φ : Set (UnaryMap A B)) (f : Operation n A B) : Prop :=
  ∃ s : Fin n, ∃ φ ∈ Φ, ∀ i x, f i x = φ i (x s)

/-- An operation is `Φ`-box-trivial if it is of dictator type or box type. -/
def IsBoxTrivial {A : ι → Type uA} {B : ι → Type uB} {n : Nat}
    (Q : Relation B) (Φ : Set (UnaryMap A B)) (f : Operation n A B) : Prop :=
  IsDictator Φ f ∨ IsBox Q f

/-- Every `n`-ary polymorphism of `(P, Q)` is `Φ`-box-trivial. -/
def BoxTrivialAtArity {A : ι → Type uA} {B : ι → Type uB}
    (P : Relation A) (Q : Relation B) (Φ : Set (UnaryMap A B)) (n : Nat) : Prop :=
  ∀ f : Operation n A B, Preserves P Q f → IsBoxTrivial Q Φ f

/-- Every positive-arity polymorphism of `(P, Q)` is `Φ`-box-trivial. -/
def BoxTrivialAtAllArities {A : ι → Type uA} {B : ι → Type uB}
    (P : Relation A) (Q : Relation B) (Φ : Set (UnaryMap A B)) : Prop :=
  ∀ n, 1 ≤ n → BoxTrivialAtArity P Q Φ n

/--
`f` is of certificate type: some coordinates of `f` are constant, and those
constant values force membership in `Q`.
-/
def IsCertificate {A : ι → Type uA} {B : ι → Type uB} {n : Nat}
    (Q : Relation B) (f : Operation n A B) : Prop :=
  ∃ I : Set ι, ∃ δ : ∀ i, i ∈ I → B i,
    (∀ i (hi : i ∈ I) x, f i x = δ i hi) ∧
    (∀ y : Tuple B, (∀ i (hi : i ∈ I), y i = δ i hi) → y ∈ Q)

/-- An operation is `Φ`-certificate-trivial if it is of dictator or certificate type. -/
def IsCertificateTrivial {A : ι → Type uA} {B : ι → Type uB} {n : Nat}
    (Q : Relation B) (Φ : Set (UnaryMap A B)) (f : Operation n A B) : Prop :=
  IsDictator Φ f ∨ IsCertificate Q f

/-- Every `n`-ary polymorphism of `(P, Q)` is `Φ`-certificate-trivial. -/
def CertificateTrivialAtArity {A : ι → Type uA} {B : ι → Type uB}
    (P : Relation A) (Q : Relation B) (Φ : Set (UnaryMap A B)) (n : Nat) : Prop :=
  ∀ f : Operation n A B, Preserves P Q f → IsCertificateTrivial Q Φ f

/-- Every positive-arity polymorphism of `(P, Q)` is `Φ`-certificate-trivial. -/
def CertificateTrivialAtAllArities {A : ι → Type uA} {B : ι → Type uB}
    (P : Relation A) (Q : Relation B) (Φ : Set (UnaryMap A B)) : Prop :=
  ∀ n, 1 ≤ n → CertificateTrivialAtArity P Q Φ n

/-- The relation `P` has full projections in every coordinate. -/
def HasFullProjections {A : ι → Type uA} (P : Relation A) : Prop :=
  ∀ i a, ∃ x ∈ P, x i = a

/-- A unary multisorted map is a polymorphism of `(P, Q)`. -/
def IsUnaryPolymorphism {A : ι → Type uA} {B : ι → Type uB}
    (P : Relation A) (Q : Relation B) (φ : UnaryMap A B) : Prop :=
  ∀ x ∈ P, (fun i ↦ φ i (x i)) ∈ Q

/-- Every component of every member of `Φ` is a bijection. -/
def IsPermutationFamily {A : ι → Type uA} (Φ : Set (UnaryMap A A)) : Prop :=
  ∀ φ ∈ Φ, ∀ i, Function.Injective (φ i) ∧ Function.Surjective (φ i)

/--
`Φ` is synchronous: two members agreeing in any one coordinate agree in all
coordinates.
-/
def IsSynchronous {A : ι → Type uA} {B : ι → Type uB}
    (Φ : Set (UnaryMap A B)) : Prop :=
  ∀ φ ∈ Φ, ∀ ψ ∈ Φ, ∀ i, φ i = ψ i → φ = ψ

/-- A type has at least two elements. -/
def HasAtLeastTwo (α : Type uA) : Prop :=
  ∃ a b : α, a ≠ b

/-- A type has exactly two elements. -/
def HasExactlyTwo (α : Type uA) : Prop :=
  ∃ a b : α, a ≠ b ∧ ∀ x, x = a ∨ x = b

/--
The unit-witness obstruction: one Boolean coordinate has a value which by
itself forces membership in `Q`.
-/
def HasUnitWitness {A : ι → Type uA} (Q : Relation A) : Prop :=
  ∃ i, ∃ b : A i, HasExactlyTwo (A i) ∧ ∀ y : Tuple A, y i = b → y ∈ Q

/--
The generalized-upset obstruction, expressed without choosing complement
operations on the two-element alphabets.

For two-element alphabets, `z i = x i ∨ z i ≠ y i` says precisely that the
`i`th coordinate is either retained from `x` or changed to the complement of
`y i`.
-/
def HasGeneralizedUpset {A : ι → Type uA}
    (P Q : Relation A) : Prop :=
  (∀ i, HasExactlyTwo (A i)) ∧
    ∃ y ∈ P, ∀ x ∈ Q, x ≠ y →
      ∀ z : Tuple A, (∀ i, z i = x i ∨ z i ≠ y i) → z ∈ Q

end BoxTriviality
