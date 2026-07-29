import BoxTriviality.ReductionToUnary
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases

/-!
# Examples

This file formalizes the two examples from the introduction of
*Triviality of promise polymorphisms*.
-/

namespace BoxTriviality

namespace BoxNotCertificate

/-- The three coordinates and the three-element alphabet in the first example. -/
abbrev Alphabet (_ : Fin 3) := Fin 3

/--
The relation consisting of all coordinate permutations of
`(0,0,0)`, `(2,2,2)`, `(0,1,1)`, and `(0,1,2)`.
-/
def relation : Relation Alphabet :=
  fun x ↦
    (∀ i, x i = 0) ∨
    (∀ i, x i = 2) ∨
    ((x 0 = 0 ∧ x 1 = 1 ∧ x 2 = 1) ∨
      (x 0 = 1 ∧ x 1 = 0 ∧ x 2 = 1) ∨
      (x 0 = 1 ∧ x 1 = 1 ∧ x 2 = 0)) ∨
    Function.Injective x

local instance relationMembershipDecidable (x : Tuple Alphabet) :
    Decidable (x ∈ relation) := by
  change Decidable (
    (∀ i, x i = 0) ∨
    (∀ i, x i = 2) ∨
    ((x 0 = 0 ∧ x 1 = 1 ∧ x 2 = 1) ∨
      (x 0 = 1 ∧ x 1 = 0 ∧ x 2 = 1) ∨
      (x 0 = 1 ∧ x 1 = 1 ∧ x 2 = 0)) ∨
    Function.Injective x)
  infer_instance

/-- The diagonal identity unary map. -/
def diagonalIdentity : UnaryMap Alphabet Alphabet := fun _ a ↦ a

/-- The singleton family `\{(\mathrm{id},\mathrm{id},\mathrm{id})\}`. -/
def identityFamily : Set (UnaryMap Alphabet Alphabet) :=
  fun φ ↦ ∀ i a, φ i a = a

local instance identityFamilyMembershipDecidable
    (φ : UnaryMap Alphabet Alphabet) : Decidable (φ ∈ identityFamily) := by
  change Decidable (∀ i a, φ i a = a)
  infer_instance

lemma relation_fullProjections : HasFullProjections relation := by
  unfold HasFullProjections
  native_decide

lemma relation_proper : ∃ z : Tuple Alphabet, z ∉ relation := by
  native_decide

lemma alphabets_haveAtLeastTwo : ∀ i, HasAtLeastTwo (Alphabet i) := by
  unfold HasAtLeastTwo
  native_decide

lemma identityFamily_permutations : IsPermutationFamily identityFamily := by
  unfold IsPermutationFamily
  native_decide

lemma identityFamily_synchronous : IsSynchronous identityFamily := by
  unfold IsSynchronous
  native_decide

/-- The finite unary verification needed to apply Theorem 1.4. -/
lemma boxTrivialAtOne :
    BoxTrivialAtArity relation relation identityFamily 1 := by
  have hclassification :
      ∀ f : Operation 1 Alphabet Alphabet,
        Preserves relation relation f →
          (∀ i x, f i x = x 0) ∨ IsBox relation f := by
    unfold Preserves applyOperation IsBox InImageBox
    native_decide
  intro f hf
  rcases hclassification f hf with hidentity | hbox
  · left
    refine ⟨0, diagonalIdentity, ?_, ?_⟩
    · intro i a
      rfl
    · intro i x
      exact hidentity i x
  · exact Or.inr hbox

lemma noUnitWitness : ¬ HasUnitWitness relation := by
  unfold HasUnitWitness HasExactlyTwo
  native_decide

lemma noGeneralizedUpset : ¬ HasGeneralizedUpset relation relation := by
  unfold HasGeneralizedUpset HasExactlyTwo
  native_decide

/--
The first relation in the introduction is box-trivial in every positive
arity with respect to the diagonal identity family.
-/
theorem boxTrivialAtAllArities :
    BoxTrivialAtAllArities relation relation identityFamily := by
  exact
    (boxTrivialAtAllArities_iff_unary_no_obstructions
      alphabets_haveAtLeastTwo (fun _ hx ↦ hx) relation_proper
      relation_fullProjections identityFamily_permutations
      identityFamily_synchronous).2
      ⟨boxTrivialAtOne, noUnitWitness, noGeneralizedUpset⟩

/--
An explicit unary polymorphism of box type which is not of certificate type.
Its coordinate images are `{0}`, `{1}`, and `{1,2}`.
-/
def nonCertificateOperation : Operation 1 Alphabet Alphabet
  | 0, _ => 0
  | 1, _ => 1
  | 2, x => if x 0 = 2 then 2 else 1

lemma nonCertificateOperation_preserves :
    Preserves relation relation nonCertificateOperation := by
  unfold Preserves applyOperation
  native_decide

lemma nonCertificateOperation_isBox :
    IsBox relation nonCertificateOperation := by
  unfold IsBox InImageBox
  native_decide

lemma nonCertificateOperation_not_dictator :
    ¬ IsDictator identityFamily nonCertificateOperation := by
  unfold IsDictator
  native_decide

lemma nonCertificateOperation_not_certificate :
    ¬ IsCertificate relation nonCertificateOperation := by
  intro hcert
  rcases hcert with ⟨I, δ, hconstant, hforce⟩
  let y : Tuple Alphabet := fun i ↦ if i = 1 then 1 else 0
  have hy : y ∈ relation := hforce y (by
    intro i hi
    fin_cases i
    · simpa [y, nonCertificateOperation] using
        hconstant 0 hi (fun _ ↦ 0)
    · simpa [y, nonCertificateOperation] using
        hconstant 1 hi (fun _ ↦ 0)
    · have hzero := hconstant 2 hi (fun _ ↦ 0)
      have htwo := hconstant 2 hi (fun _ ↦ 2)
      have hne : (1 : Fin 3) ≠ 2 := by decide
      exact False.elim (hne (by
        simpa [nonCertificateOperation] using hzero.trans htwo.symm)))
  have hyNot : y ∉ relation := by
    native_decide
  exact hyNot hy

/--
Thus the relation is not certificate-trivial even at unary arity.
-/
theorem not_certificateTrivialAtOne :
    ¬ CertificateTrivialAtArity relation relation identityFamily 1 := by
  intro htrivial
  rcases htrivial nonCertificateOperation
      nonCertificateOperation_preserves with hdict | hcert
  · exact nonCertificateOperation_not_dictator hdict
  · exact nonCertificateOperation_not_certificate hcert

end BoxNotCertificate

namespace DifferentAlphabetsCounterexample

/-- The Boolean input alphabets in the counterexample from the remark. -/
abbrev InputAlphabet (_ : Fin 3) := Fin 2

/-- The three-element output alphabets in the counterexample from the remark. -/
abbrev OutputAlphabet (_ : Fin 3) := Fin 3

/-- The Boolean relation with the two constant tuples removed. -/
def inputRelation : Relation InputAlphabet :=
  fun x ↦ ¬ (∀ i, x i = 0) ∧ ¬ (∀ i, x i = 1)

local instance inputRelationMembershipDecidable (x : Tuple InputAlphabet) :
    Decidable (x ∈ inputRelation) := by
  change Decidable (¬ (∀ i, x i = 0) ∧ ¬ (∀ i, x i = 1))
  infer_instance

/--
The output relation: the embedded input relation, together with all nonzero
tuples over `{0,2}`.
-/
def outputRelation : Relation OutputAlphabet :=
  fun y ↦
    ((∀ i, y i = 0 ∨ y i = 1) ∧
      ¬ (∀ i, y i = 0) ∧ ¬ (∀ i, y i = 1)) ∨
    ((∀ i, y i = 0 ∨ y i = 2) ∧ ¬ (∀ i, y i = 0))

local instance outputRelationMembershipDecidable (y : Tuple OutputAlphabet) :
    Decidable (y ∈ outputRelation) := by
  change Decidable (
    ((∀ i, y i = 0 ∨ y i = 1) ∧
      ¬ (∀ i, y i = 0) ∧ ¬ (∀ i, y i = 1)) ∨
    ((∀ i, y i = 0 ∨ y i = 2) ∧ ¬ (∀ i, y i = 0)))
  infer_instance

/--
The family of diagonal injections whose image contains zero.
-/
def injectionFamily : Set (UnaryMap InputAlphabet OutputAlphabet) :=
  fun ψ ↦ ∃ φ : Fin 2 → Fin 3,
    Function.Injective φ ∧ (∃ a, φ a = 0) ∧ ψ = fun _ ↦ φ

local instance injectionFamilyMembershipDecidable
    (ψ : UnaryMap InputAlphabet OutputAlphabet) :
    Decidable (ψ ∈ injectionFamily) := by
  change Decidable (∃ φ : Fin 2 → Fin 3,
    Function.Injective φ ∧ (∃ a, φ a = 0) ∧ ψ = fun _ ↦ φ)
  infer_instance

/-- The natural inclusion of the Boolean alphabet into the three-element alphabet. -/
def inclusion (a : Fin 2) : Fin 3 :=
  ⟨a.val, Nat.lt_of_lt_of_le a.isLt (by decide)⟩

/-- The natural inclusion in every coordinate. -/
def diagonalInclusion : UnaryMap InputAlphabet OutputAlphabet :=
  fun _ ↦ inclusion

lemma diagonalInclusion_mem : diagonalInclusion ∈ injectionFamily := by
  change ∃ φ : Fin 2 → Fin 3,
    Function.Injective φ ∧ (∃ a, φ a = 0) ∧
      diagonalInclusion = fun _ ↦ φ
  refine ⟨inclusion, ?_, ⟨0, rfl⟩, rfl⟩
  unfold inclusion
  native_decide

/--
The natural inclusion is the injective homomorphism from the input relation
to the output relation mentioned in the remark.
-/
lemma diagonalInclusion_polymorphism :
    IsUnaryPolymorphism inputRelation outputRelation diagonalInclusion := by
  change ∀ x : Tuple InputAlphabet, inputRelation x →
    outputRelation (fun i ↦ inclusion (x i))
  unfold inputRelation outputRelation inclusion
  native_decide

/--
The finite verification that the relation pair in the remark is unary
box-trivial.
-/
theorem boxTrivialAtOne :
    BoxTrivialAtArity inputRelation outputRelation injectionFamily 1 := by
  unfold BoxTrivialAtArity Preserves applyOperation IsBoxTrivial
    IsDictator IsBox InImageBox
  native_decide

/--
The binary operation from the remark: it returns zero precisely on `(1,1)`
and returns two otherwise, in every coordinate.
-/
def binaryOperation : Operation 2 InputAlphabet OutputAlphabet :=
  fun _ x ↦ if x 0 = 1 ∧ x 1 = 1 then 0 else 2

lemma binaryOperation_preserves :
    Preserves inputRelation outputRelation binaryOperation := by
  unfold Preserves applyOperation
  native_decide

lemma binaryOperation_not_boxTrivial :
    ¬ IsBoxTrivial outputRelation injectionFamily binaryOperation := by
  unfold IsBoxTrivial IsDictator IsBox InImageBox
  native_decide

/--
Despite unary box-triviality, the relation pair is not box-trivial at arity
two.
-/
theorem not_boxTrivialAtTwo :
    ¬ BoxTrivialAtArity inputRelation outputRelation injectionFamily 2 := by
  intro htrivial
  exact binaryOperation_not_boxTrivial
    (htrivial binaryOperation binaryOperation_preserves)

end DifferentAlphabetsCounterexample

end BoxTriviality
