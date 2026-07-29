import BoxTriviality.ReductionToBinary

/-!
# Reduction to unary

This file formalizes Theorem 1.4 of *Triviality of promise polymorphisms*.
-/

namespace BoxTriviality

universe uι uA

variable {ι : Type uι}
variable {A : ι → Type uA}
variable {P Q : Relation A}
variable {Φ : Set (UnaryMap A A)}

/-- Regard a unary multisorted map as a one-ary operation. -/
def unaryOperation (φ : UnaryMap A A) : Operation 1 A A :=
  fun i x ↦ φ i (x 0)

/-- The box-type condition, stated directly for a unary multisorted map. -/
def UnaryIsBox (Q : Relation A) (φ : UnaryMap A A) : Prop :=
  ∀ ⦃y⦄, (∀ i, ∃ a, φ i a = y i) → y ∈ Q

/-- The direct unary and operation formulations of preservation agree. -/
lemma preserves_unaryOperation_iff (φ : UnaryMap A A) :
    Preserves P Q (unaryOperation φ) ↔ IsUnaryPolymorphism P Q φ := by
  constructor
  · intro h x hx
    let rows : Fin 1 → Tuple A := fun _ ↦ x
    simpa [IsUnaryPolymorphism, applyOperation, unaryOperation, rows] using
      h rows (fun _ ↦ hx)
  · intro h rows hrows
    simpa [IsUnaryPolymorphism, applyOperation, unaryOperation] using
      h (rows 0) (hrows 0)

/--
Unary box-triviality says exactly that every unary polymorphism either belongs
to the distinguished family or has box type.
-/
lemma unary_classification
    (hunary : BoxTrivialAtArity P Q Φ 1)
    {φ : UnaryMap A A} (hφ : IsUnaryPolymorphism P Q φ) :
    φ ∈ Φ ∨ UnaryIsBox Q φ := by
  rcases hunary (unaryOperation φ)
      ((preserves_unaryOperation_iff φ).2 hφ) with hdict | hbox
  · left
    rcases hdict with ⟨s, ψ, hψ, heq⟩
    have hs : s = 0 := Fin.eq_zero s
    subst s
    have hφψ : φ = ψ := by
      funext i a
      let x : Fin 1 → A i := fun _ ↦ a
      simpa [unaryOperation, x] using heq i x
    simpa [hφψ] using hψ
  · right
    intro y hy
    apply hbox
    intro i
    rcases hy i with ⟨a, ha⟩
    let x : Fin 1 → A i := fun _ ↦ a
    exact ⟨x, by simpa [unaryOperation, x] using ha⟩

/--
A member of a permutation family cannot have unary box type when `Q` is a
proper subset of the full product.
-/
lemma member_not_unaryIsBox
    (hperm : IsPermutationFamily Φ)
    (hproper : ∃ z : Tuple A, z ∉ Q)
    {φ : UnaryMap A A} (hφ : φ ∈ Φ) :
    ¬ UnaryIsBox Q φ := by
  intro hbox
  rcases hproper with ⟨z, hz⟩
  apply hz
  apply hbox
  intro i
  rcases (hperm φ hφ i).2 (z i) with ⟨a, ha⟩
  exact ⟨a, ha⟩

/--
Consequently the unary classification is exclusive: a unary polymorphism is
in `Φ` exactly when it is not of box type.
-/
lemma unary_mem_iff_not_box
    (hunary : BoxTrivialAtArity P Q Φ 1)
    (hperm : IsPermutationFamily Φ)
    (hproper : ∃ z : Tuple A, z ∉ Q)
    {φ : UnaryMap A A} (hφ : IsUnaryPolymorphism P Q φ) :
    φ ∈ Φ ↔ ¬ UnaryIsBox Q φ := by
  constructor
  · exact member_not_unaryIsBox hperm hproper
  · intro hnbox
    rcases unary_classification hunary hφ with hmem | hbox
    · exact hmem
    · exact False.elim (hnbox hbox)

/-- Package two values as the two inputs of a binary coordinate operation. -/
def binaryPair {α : Type uA} (a b : α) : Fin 2 → α :=
  Fin.cases a (fun _ ↦ b)

@[simp] lemma binaryPair_zero {α : Type uA} (a b : α) :
    binaryPair a b 0 = a := rfl

@[simp] lemma binaryPair_one {α : Type uA} (a b : α) :
    binaryPair a b 1 = b := rfl

@[simp] lemma binaryPair_eta {α : Type uA} (x : Fin 2 → α) :
    binaryPair (x 0) (x 1) = x := by
  funext r
  refine Fin.cases rfl (fun s ↦ ?_) r
  have hs : s = 0 := Fin.eq_zero s
  subst s
  rfl

/-- A binary operation with its first input fixed to a tuple. -/
def firstSection (f : Operation 2 A A) (x : Tuple A) : UnaryMap A A :=
  fun i a ↦ f i (binaryPair (x i) a)

/-- A binary operation with its second input fixed to a tuple. -/
def secondSection (f : Operation 2 A A) (x : Tuple A) : UnaryMap A A :=
  fun i a ↦ f i (binaryPair a (x i))

/-- Fixing a `P`-input of a binary polymorphism gives a unary polymorphism. -/
lemma firstSection_isUnaryPolymorphism
    {f : Operation 2 A A} (hf : Preserves P Q f)
    {x : Tuple A} (hx : x ∈ P) :
    IsUnaryPolymorphism P Q (firstSection f x) := by
  intro y hy
  let rows : Fin 2 → Tuple A := Fin.cases x (fun _ ↦ y)
  have hrows : ∀ r, rows r ∈ P := by
    intro r
    refine Fin.cases hx (fun s ↦ ?_) r
    simpa [rows] using hy
  have heq :
      applyOperation f rows =
        (fun i ↦ f i (binaryPair (x i) (y i))) := by
    funext i
    apply congrArg (f i)
    funext r
    refine Fin.cases rfl (fun s ↦ ?_) r
    have hs : s = 0 := Fin.eq_zero s
    subst s
    rfl
  change (fun i ↦ f i (binaryPair (x i) (y i))) ∈ Q
  rw [← heq]
  exact hf rows hrows

/-- Fixing the other input of a binary polymorphism gives a unary polymorphism. -/
lemma secondSection_isUnaryPolymorphism
    {f : Operation 2 A A} (hf : Preserves P Q f)
    {x : Tuple A} (hx : x ∈ P) :
    IsUnaryPolymorphism P Q (secondSection f x) := by
  intro y hy
  let rows : Fin 2 → Tuple A := Fin.cases y (fun _ ↦ x)
  have hrows : ∀ r, rows r ∈ P := by
    intro r
    refine Fin.cases hy (fun s ↦ ?_) r
    simpa [rows] using hx
  have heq :
      applyOperation f rows =
        (fun i ↦ f i (binaryPair (y i) (x i))) := by
    funext i
    apply congrArg (f i)
    funext r
    refine Fin.cases rfl (fun s ↦ ?_) r
    have hs : s = 0 := Fin.eq_zero s
    subst s
    rfl
  change (fun i ↦ f i (binaryPair (y i) (x i))) ∈ Q
  rw [← heq]
  exact hf rows hrows

/-- Every first section of a binary polymorphism has the unary dichotomy. -/
lemma firstSection_classification
    (hunary : BoxTrivialAtArity P Q Φ 1)
    {f : Operation 2 A A} (hf : Preserves P Q f)
    {x : Tuple A} (hx : x ∈ P) :
    firstSection f x ∈ Φ ∨ UnaryIsBox Q (firstSection f x) :=
  unary_classification hunary (firstSection_isUnaryPolymorphism hf hx)

/-- Every second section of a binary polymorphism has the unary dichotomy. -/
lemma secondSection_classification
    (hunary : BoxTrivialAtArity P Q Φ 1)
    {f : Operation 2 A A} (hf : Preserves P Q f)
    {x : Tuple A} (hx : x ∈ P) :
    secondSection f x ∈ Φ ∨ UnaryIsBox Q (secondSection f x) :=
  unary_classification hunary (secondSection_isUnaryPolymorphism hf hx)

/-- Whether one coordinate section of a binary operation is a permutation. -/
def FirstSectionIsPermutation (f : Operation 2 A A) (i : ι) (a : A i) : Prop :=
  Function.Bijective (fun b ↦ f i (binaryPair a b))

/--
Normalize a binary operation by replacing every permutation-valued first
section by the identity, while leaving all other sections unchanged.
-/
noncomputable def normalizeFirstSections (f : Operation 2 A A) :
    Operation 2 A A := by
  classical
  intro i input
  exact if FirstSectionIsPermutation f i (input 0)
    then input 1 else f i input

@[simp] lemma normalizeFirstSections_of_permutation
    (f : Operation 2 A A) (i : ι) (a b : A i)
    (hperm : FirstSectionIsPermutation f i a) :
    normalizeFirstSections f i (binaryPair a b) = b := by
  classical
  simp [normalizeFirstSections, hperm]

@[simp] lemma normalizeFirstSections_of_not_permutation
    (f : Operation 2 A A) (i : ι) (a b : A i)
    (hperm : ¬ FirstSectionIsPermutation f i a) :
    normalizeFirstSections f i (binaryPair a b) =
      f i (binaryPair a b) := by
  classical
  simp [normalizeFirstSections, hperm]

/-- A permutation first section becomes the identity under normalization. -/
lemma normalized_firstSection_eq_identity
    {f : Operation 2 A A} {x : Tuple A}
    (hperm : ∀ i, FirstSectionIsPermutation f i (x i)) :
    firstSection (normalizeFirstSections f) x =
      (fun _ a ↦ a) := by
  funext i a
  simp [firstSection, hperm i]

/--
For every fixed first input, normalization preserves each coordinate image.
-/
lemma normalized_firstSection_image_iff
    {f : Operation 2 A A} (i : ι) (a value : A i) :
    (∃ b, normalizeFirstSections f i (binaryPair a b) = value) ↔
      ∃ b, f i (binaryPair a b) = value := by
  classical
  by_cases hperm : FirstSectionIsPermutation f i a
  · constructor
    · intro h
      rcases h with ⟨b, hb⟩
      have hbvalue : b = value := by
        simpa [normalizeFirstSections_of_permutation f i a b hperm] using hb
      rcases hperm.2 value with ⟨c, hc⟩
      exact ⟨c, hc⟩
    · intro h
      exact ⟨value, by
        simp [normalizeFirstSections_of_permutation f i a value hperm]⟩
  · simp [normalizeFirstSections_of_not_permutation f i a, hperm]

/--
The normalized operation has the same full coordinate images as the original
operation.
-/
lemma normalizeFirstSections_inImageBox_iff
    {f : Operation 2 A A} {y : Tuple A} :
    InImageBox (normalizeFirstSections f) y ↔ InImageBox f y := by
  classical
  constructor
  · intro hy i
    rcases hy i with ⟨input, hinput⟩
    rw [← binaryPair_eta input] at hinput
    rcases (normalized_firstSection_image_iff i (input 0) (y i)).1
      ⟨input 1, hinput⟩ with ⟨b, hb⟩
    exact ⟨binaryPair (input 0) b, hb⟩
  · intro hy i
    rcases hy i with ⟨input, hinput⟩
    rw [← binaryPair_eta input] at hinput
    rcases (normalized_firstSection_image_iff i (input 0) (y i)).2
      ⟨input 1, hinput⟩ with ⟨b, hb⟩
    exact ⟨binaryPair (input 0) b, hb⟩

/-- Normalization preserves box type in both directions. -/
lemma normalizeFirstSections_isBox_iff
    {f : Operation 2 A A} :
    IsBox Q (normalizeFirstSections f) ↔ IsBox Q f := by
  constructor
  · intro hbox y hy
    exact hbox ((normalizeFirstSections_inImageBox_iff).2 hy)
  · intro hbox y hy
    exact hbox ((normalizeFirstSections_inImageBox_iff).1 hy)

/--
Normalization preserves polymorphisms when all unary polymorphisms have the
`Φ`/box dichotomy and members of `Φ` are coordinatewise permutations.
-/
lemma normalizeFirstSections_preserves
    (hunary : BoxTrivialAtArity P Q Φ 1)
    (hPQ : P ⊆ Q)
    (hperm : IsPermutationFamily Φ)
    {f : Operation 2 A A} (hf : Preserves P Q f) :
    Preserves P Q (normalizeFirstSections f) := by
  intro rows hrows
  rcases firstSection_classification hunary hf (hrows 0) with hmem | hbox
  · have hallperm : ∀ i,
        FirstSectionIsPermutation f i (rows 0 i) := by
      intro i
      exact hperm (firstSection f (rows 0)) hmem i
    have hout : applyOperation (normalizeFirstSections f) rows = rows 1 := by
      funext i
      change normalizeFirstSections f i (fun r ↦ rows r i) = rows 1 i
      rw [← binaryPair_eta (fun r ↦ rows r i)]
      exact normalizeFirstSections_of_permutation
        f i (rows 0 i) (rows 1 i) (hallperm i)
    rw [hout]
    exact hPQ (hrows 1)
  · apply hbox
    intro i
    change ∃ a, firstSection f (rows 0) i a =
      applyOperation (normalizeFirstSections f) rows i
    change ∃ a, f i (binaryPair (rows 0 i) a) =
      normalizeFirstSections f i (fun r ↦ rows r i)
    rw [← binaryPair_eta (fun r ↦ rows r i)]
    exact (normalized_firstSection_image_iff
      i (rows 0 i)
      (normalizeFirstSections f i
        (binaryPair (rows 0 i) (rows 1 i)))).1
      ⟨rows 1 i, rfl⟩

/--
A unary box map over a proper relation must fail to be surjective in some
coordinate.
-/
lemma exists_not_surjective_of_unaryIsBox
    (hproper : ∃ z : Tuple A, z ∉ Q)
    {φ : UnaryMap A A} (hbox : UnaryIsBox Q φ) :
    ∃ i, ¬ Function.Surjective (φ i) := by
  classical
  by_contra hnone
  rcases hproper with ⟨z, hz⟩
  apply hz
  apply hbox
  intro i
  have hsurj : Function.Surjective (φ i) := by
    by_contra hnsurj
    exact hnone ⟨i, hnsurj⟩
  exact hsurj (z i)

/--
The normalization setup for a mixed pair of sections. At the `Φ`-section it
is the identity; at the box section one coordinate visibly depends on the
first input. Its full coordinate images remain those of the original `f`.
-/
lemma mixedNormalization_setup
    (hunary : BoxTrivialAtArity P Q Φ 1)
    (hPQ : P ⊆ Q)
    (hproper : ∃ z : Tuple A, z ∉ Q)
    (hperm : IsPermutationFamily Φ)
    {f : Operation 2 A A} (hf : Preserves P Q f)
    {σ τ : Tuple A}
    (hσbox : UnaryIsBox Q (firstSection f σ))
    (hτmem : firstSection f τ ∈ Φ) :
    Preserves P Q (normalizeFirstSections f) ∧
      firstSection (normalizeFirstSections f) τ = (fun _ a ↦ a) ∧
      (∃ i κ,
        normalizeFirstSections f i (binaryPair (τ i) κ) = κ ∧
        normalizeFirstSections f i (binaryPair (σ i) κ) ≠ κ) ∧
      (∀ y, InImageBox (normalizeFirstSections f) y ↔ InImageBox f y) := by
  have hτperm : ∀ i, FirstSectionIsPermutation f i (τ i) := by
    intro i
    exact hperm (firstSection f τ) hτmem i
  have hτid :
      firstSection (normalizeFirstSections f) τ = (fun _ a ↦ a) :=
    normalized_firstSection_eq_identity hτperm
  rcases exists_not_surjective_of_unaryIsBox hproper hσbox with
    ⟨i, hi⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : A i,
      ∀ a, firstSection f σ i a ≠ κ := by
    by_contra hnone
    apply hi
    intro value
    by_contra hnpreimage
    exact hnone ⟨value, fun a ha ↦ hnpreimage ⟨a, ha⟩⟩
  have hσnotperm : ¬ FirstSectionIsPermutation f i (σ i) := by
    intro hpermσ
    exact hi hpermσ.2
  refine ⟨normalizeFirstSections_preserves hunary hPQ hperm hf,
    hτid, ?_, fun y ↦ normalizeFirstSections_inImageBox_iff⟩
  refine ⟨i, κ, ?_, ?_⟩
  · exact normalizeFirstSections_of_permutation
      f i (τ i) κ (hτperm i)
  · rw [normalizeFirstSections_of_not_permutation
      f i (σ i) κ hσnotperm]
    exact hκ κ

/--
In the genuinely mixed, non-box case, the normalized operation is not
`Φ`-box-trivial: the identity section witnesses dependence on the second
input, while the exceptional box section witnesses dependence on the first.
-/
lemma mixedNormalization_not_boxTrivial
    [Nonempty ι]
    (hA : ∀ i, HasAtLeastTwo (A i))
    (hunary : BoxTrivialAtArity P Q Φ 1)
    (hPQ : P ⊆ Q)
    (hproper : ∃ z : Tuple A, z ∉ Q)
    (hperm : IsPermutationFamily Φ)
    {f : Operation 2 A A} (hf : Preserves P Q f)
    {σ τ : Tuple A}
    (hσbox : UnaryIsBox Q (firstSection f σ))
    (hτmem : firstSection f τ ∈ Φ)
    (hfnotbox : ¬ IsBox Q f) :
    ¬ IsBoxTrivial Q Φ (normalizeFirstSections f) := by
  rcases mixedNormalization_setup
      hunary hPQ hproper hperm hf hσbox hτmem with
    ⟨hnormpoly, hτid, ⟨i, κ, hτκ, hσκ⟩, himage⟩
  intro htrivial
  rcases htrivial with hdict | hbox
  · rcases hdict with ⟨s, φ, hφmem, hφ⟩
    have hs : s = 0 ∨ s = 1 := by
      refine Fin.cases (Or.inl rfl) (fun q ↦ ?_) s
      have hq : q = 0 := Fin.eq_zero q
      subst q
      exact Or.inr rfl
    rcases hs with hs | hs
    · subst s
      let j : ι := Classical.choice inferInstance
      rcases hA j with ⟨a, b, hab⟩
      let inputA : Fin 2 → A j := binaryPair (τ j) a
      let inputB : Fin 2 → A j := binaryPair (τ j) b
      have heq :
          normalizeFirstSections f j inputA =
            normalizeFirstSections f j inputB := by
        rw [hφ j inputA, hφ j inputB]
        rfl
      have houtA : normalizeFirstSections f j inputA = a := by
        change firstSection (normalizeFirstSections f) τ j a = a
        rw [hτid]
      have houtB : normalizeFirstSections f j inputB = b := by
        change firstSection (normalizeFirstSections f) τ j b = b
        rw [hτid]
      exact hab (houtA.symm.trans (heq.trans houtB))
    · subst s
      let inputτ : Fin 2 → A i := binaryPair (τ i) κ
      let inputσ : Fin 2 → A i := binaryPair (σ i) κ
      have heq :
          normalizeFirstSections f i inputτ =
            normalizeFirstSections f i inputσ := by
        rw [hφ i inputτ, hφ i inputσ]
        rfl
      exact hσκ (heq.symm ▸ hτκ)
  · exact hfnotbox ((normalizeFirstSections_isBox_iff).1 hbox)

/-- Swap the two inputs of a binary operation. -/
def transposeBinary (f : Operation 2 A A) : Operation 2 A A :=
  fun i input ↦ f i (binaryPair (input 1) (input 0))

@[simp] lemma transposeBinary_pair
    (f : Operation 2 A A) (i : ι) (a b : A i) :
    transposeBinary f i (binaryPair a b) =
      f i (binaryPair b a) := rfl

@[simp] lemma transposeBinary_involutive (f : Operation 2 A A) :
    transposeBinary (transposeBinary f) = f := by
  funext i input
  rw [← binaryPair_eta input]
  rfl

/-- First sections of the transpose are second sections of the original. -/
lemma firstSection_transposeBinary
    (f : Operation 2 A A) (x : Tuple A) :
    firstSection (transposeBinary f) x = secondSection f x := by
  funext i a
  rfl

/-- Transposing a binary polymorphism preserves the polymorphism property. -/
lemma transposeBinary_preserves
    {f : Operation 2 A A} (hf : Preserves P Q f) :
    Preserves P Q (transposeBinary f) := by
  intro rows hrows
  let swapped : Fin 2 → Tuple A :=
    Fin.cases (rows 1) (fun _ ↦ rows 0)
  have hswapped : ∀ r, swapped r ∈ P := by
    intro r
    refine Fin.cases (hrows 1) (fun s ↦ ?_) r
    have hs : s = 0 := Fin.eq_zero s
    subst s
    exact hrows 0
  have heq :
      applyOperation (transposeBinary f) rows =
        applyOperation f swapped := by
    funext i
    change f i (binaryPair (rows 1 i) (rows 0 i)) =
      f i (fun r ↦ swapped r i)
    apply congrArg (f i)
    funext r
    refine Fin.cases rfl (fun s ↦ ?_) r
    have hs : s = 0 := Fin.eq_zero s
    subst s
    rfl
  rw [heq]
  exact hf swapped hswapped

/-- Transposition preserves the full coordinate image box. -/
lemma transposeBinary_inImageBox_iff
    {f : Operation 2 A A} {y : Tuple A} :
    InImageBox (transposeBinary f) y ↔ InImageBox f y := by
  constructor
  · intro hy i
    rcases hy i with ⟨input, hinput⟩
    exact ⟨binaryPair (input 1) (input 0), hinput⟩
  · intro hy i
    rcases hy i with ⟨input, hinput⟩
    refine ⟨binaryPair (input 1) (input 0), ?_⟩
    simpa [transposeBinary] using hinput

/-- Transposition preserves box type. -/
lemma transposeBinary_isBox_iff
    {f : Operation 2 A A} :
    IsBox Q (transposeBinary f) ↔ IsBox Q f := by
  constructor
  · intro hbox y hy
    exact hbox ((transposeBinary_inImageBox_iff).2 hy)
  · intro hbox y hy
    exact hbox ((transposeBinary_inImageBox_iff).1 hy)

/-- Transposition exchanges the two possible dictator coordinates. -/
lemma transposeBinary_isDictator_iff
    {f : Operation 2 A A} :
    IsDictator Φ (transposeBinary f) ↔ IsDictator Φ f := by
  have forward : ∀ g : Operation 2 A A,
      IsDictator Φ g → IsDictator Φ (transposeBinary g) := by
    intro g hg
    rcases hg with ⟨s, φ, hφmem, hφ⟩
    have hs : s = 0 ∨ s = 1 := by
      refine Fin.cases (Or.inl rfl) (fun q ↦ ?_) s
      have hq : q = 0 := Fin.eq_zero q
      subst q
      exact Or.inr rfl
    rcases hs with hs | hs
    · subst s
      refine ⟨1, φ, hφmem, ?_⟩
      intro i input
      rw [← binaryPair_eta input]
      simp [transposeBinary, hφ]
    · subst s
      refine ⟨0, φ, hφmem, ?_⟩
      intro i input
      rw [← binaryPair_eta input]
      simp [transposeBinary, hφ]
  constructor
  · intro h
    have ht := forward (transposeBinary f) h
    simpa using ht
  · exact forward f

/-- Transposition preserves `Φ`-box-triviality. -/
lemma transposeBinary_isBoxTrivial_iff
    {f : Operation 2 A A} :
    IsBoxTrivial Q Φ (transposeBinary f) ↔ IsBoxTrivial Q Φ f := by
  exact or_congr transposeBinary_isDictator_iff transposeBinary_isBox_iff

/--
If all first and second sections belong to a synchronous permutation family,
then two members of `P` agreeing in one coordinate agree everywhere.
-/
lemma eq_of_eq_coordinate_of_allSections_mem
    (hperm : IsPermutationFamily Φ)
    (hsync : IsSynchronous Φ)
    {f : Operation 2 A A}
    (hfirst : ∀ x ∈ P, firstSection f x ∈ Φ)
    (hsecond : ∀ x ∈ P, secondSection f x ∈ Φ)
    {z w : Tuple A} (hz : z ∈ P) (hw : w ∈ P)
    (i : ι) (hi : z i = w i) :
    z = w := by
  have hfirstEq : firstSection f z = firstSection f w := by
    apply hsync (firstSection f z) (hfirst z hz)
      (firstSection f w) (hfirst w hw) i
    funext a
    simp [firstSection, hi]
  funext j
  apply (hperm (secondSection f z) (hsecond z hz) j).1
  change f j (binaryPair (z j) (z j)) =
    f j (binaryPair (w j) (z j))
  exact congrFun (congrFun hfirstEq j) (z j)

/--
Under the preceding separation property and full projections, every alphabet
symbol has a unique completion to a member of `P`.
-/
lemma existsUnique_completion
    (hfull : HasFullProjections P)
    (hseparate : ∀ {z w : Tuple A}, z ∈ P → w ∈ P →
      ∀ i, z i = w i → z = w)
    (i : ι) (a : A i) :
    ∃! x : Tuple A, x ∈ P ∧ x i = a := by
  rcases hfull i a with ⟨x, hx, hxi⟩
  refine ⟨x, ⟨hx, hxi⟩, ?_⟩
  intro y hy
  exact hseparate hy.1 hx i (hy.2.trans hxi.symm)

/-- The unique member of `P` having a prescribed value in one coordinate. -/
noncomputable def completion
    (hfull : HasFullProjections P)
    (hseparate : ∀ {z w : Tuple A}, z ∈ P → w ∈ P →
      ∀ i, z i = w i → z = w)
    (i : ι) (a : A i) : Tuple A :=
  Classical.choose (existsUnique_completion hfull hseparate i a)

lemma completion_mem
    (hfull : HasFullProjections P)
    (hseparate : ∀ {z w : Tuple A}, z ∈ P → w ∈ P →
      ∀ i, z i = w i → z = w)
    (i : ι) (a : A i) :
    completion hfull hseparate i a ∈ P :=
  (Classical.choose_spec
    (existsUnique_completion hfull hseparate i a)).1.1

@[simp] lemma completion_at
    (hfull : HasFullProjections P)
    (hseparate : ∀ {z w : Tuple A}, z ∈ P → w ∈ P →
      ∀ i, z i = w i → z = w)
    (i : ι) (a : A i) :
    completion hfull hseparate i a i = a :=
  (Classical.choose_spec
    (existsUnique_completion hfull hseparate i a)).1.2

lemma completion_eq_of_mem
    (hfull : HasFullProjections P)
    (hseparate : ∀ {z w : Tuple A}, z ∈ P → w ∈ P →
      ∀ i, z i = w i → z = w)
    {x : Tuple A} (hx : x ∈ P) (i : ι) :
    completion hfull hseparate i (x i) = x := by
  exact hseparate (completion_mem hfull hseparate i (x i)) hx i
    (completion_at hfull hseparate i (x i))

/-- Transport alphabet symbols between two coordinates using their unique completions. -/
noncomputable def coordinateMap
    (hfull : HasFullProjections P)
    (hseparate : ∀ {z w : Tuple A}, z ∈ P → w ∈ P →
      ∀ i, z i = w i → z = w)
    (i j : ι) : A i → A j :=
  fun a ↦ completion hfull hseparate i a j

/-- The coordinate transport map is injective. -/
lemma coordinateMap_injective
    (hfull : HasFullProjections P)
    (hseparate : ∀ {z w : Tuple A}, z ∈ P → w ∈ P →
      ∀ i, z i = w i → z = w)
    (i j : ι) :
    Function.Injective (coordinateMap hfull hseparate i j) := by
  intro a b hab
  have htuples : completion hfull hseparate i a =
      completion hfull hseparate i b :=
    hseparate
      (completion_mem hfull hseparate i a)
      (completion_mem hfull hseparate i b) j hab
  have hat := congrFun htuples i
  simpa using hat

/-- The coordinate transport map is surjective. -/
lemma coordinateMap_surjective
    (hfull : HasFullProjections P)
    (hseparate : ∀ {z w : Tuple A}, z ∈ P → w ∈ P →
      ∀ i, z i = w i → z = w)
    (i j : ι) :
    Function.Surjective (coordinateMap hfull hseparate i j) := by
  intro b
  let x := completion hfull hseparate j b
  refine ⟨x i, ?_⟩
  change completion hfull hseparate i (x i) j = b
  rw [completion_eq_of_mem hfull hseparate
    (completion_mem hfull hseparate j b) i]
  exact completion_at hfull hseparate j b

/-- In a type with two distinct elements, every chosen element has a distinct peer. -/
lemma exists_ne_of_hasAtLeastTwo
    {α : Type uι} (hα : HasAtLeastTwo α) (i : α) :
    ∃ j, j ≠ i := by
  rcases hα with ⟨a, b, hab⟩
  by_cases hai : a = i
  · exact ⟨b, fun hbi ↦ hab (hai.trans hbi.symm)⟩
  · exact ⟨a, hai⟩

/--
A unary map chooses from the first-input sections of `f` if each value
`g i a` lies in the image of the section obtained by fixing the first input
to `a`.
-/
def ChoosesFirstSections (f : Operation 2 A A) (g : UnaryMap A A) : Prop :=
  ∀ i a, ∃ b, f i (binaryPair a b) = g i a

/--
If every first section over a member of `P` has box type, then every map which
chooses pointwise from those sections is a unary polymorphism.
-/
lemma choosingFirstSections_isUnaryPolymorphism
    {f : Operation 2 A A}
    (hsections : ∀ x ∈ P, UnaryIsBox Q (firstSection f x))
    {g : UnaryMap A A} (hg : ChoosesFirstSections f g) :
    IsUnaryPolymorphism P Q g := by
  intro x hx
  apply hsections x hx
  intro i
  rcases hg i (x i) with ⟨b, hb⟩
  exact ⟨b, by simpa [firstSection] using hb⟩

/-- Failure of binary box type supplies a tuple outside `Q` in the image box. -/
lemma exists_image_witness_of_not_box
    {f : Operation 2 A A} (hf : ¬ IsBox Q f) :
    ∃ ω : Tuple A, ω ∉ Q ∧ InImageBox f ω := by
  classical
  by_contra hnot
  apply hf
  intro y hy
  by_contra hyQ
  exact hnot ⟨y, hyQ, hy⟩

/--
Choose one value from every first section while forcing a prescribed image-box
witness `ω` to occur at a tuple `α`.
-/
lemma exists_firstSection_selection
    (hA : ∀ i, HasAtLeastTwo (A i))
    {f : Operation 2 A A} {ω : Tuple A}
    (hω : InImageBox f ω) :
    ∃ α : Tuple A, ∃ g : UnaryMap A A,
      ChoosesFirstSections f g ∧ ∀ i, g i (α i) = ω i := by
  classical
  choose col hcol using hω
  let α : Tuple A := fun i ↦ col i 0
  let d : Tuple A := fun i ↦ Classical.choose (hA i)
  let g : UnaryMap A A := fun i a ↦
    if a = α i then ω i else f i (binaryPair a (d i))
  refine ⟨α, g, ?_, ?_⟩
  · intro i a
    by_cases hai : a = α i
    · subst a
      refine ⟨col i 1, ?_⟩
      simpa [g, α] using hcol i
    · exact ⟨d i, by simp [g, hai]⟩
  · intro i
    simp [g]

/--
The selection forced through a tuple `ω ∉ Q` belongs to `Φ`: it is a unary
polymorphism, and the occurrence of `ω` rules out unary box type.
-/
lemma firstSection_selection_mem
    (hunary : BoxTrivialAtArity P Q Φ 1)
    {f : Operation 2 A A}
    (hsections : ∀ x ∈ P, UnaryIsBox Q (firstSection f x))
    {ω α : Tuple A} (hωQ : ω ∉ Q)
    {g : UnaryMap A A}
    (hg : ChoosesFirstSections f g)
    (hgω : ∀ i, g i (α i) = ω i) :
    g ∈ Φ := by
  have hgpoly : IsUnaryPolymorphism P Q g :=
    choosingFirstSections_isUnaryPolymorphism hsections hg
  rcases unary_classification hunary hgpoly with hmem | hbox
  · exact hmem
  · exact False.elim (hωQ (hbox (fun i ↦ ⟨α i, hgω i⟩)))

/-- Change one value of one component of a unary multisorted map. -/
noncomputable def modifyUnary (g : UnaryMap A A) (i : ι)
    (a value : A i) : UnaryMap A A := by
  classical
  intro j
  by_cases hji : j = i
  · subst j
    exact fun x ↦ if x = a then value else g i x
  · exact g j

@[simp] lemma modifyUnary_at_eq (g : UnaryMap A A) (i : ι)
    (a value : A i) :
    modifyUnary g i a value i a = value := by
  classical
  simp [modifyUnary]

@[simp] lemma modifyUnary_at_ne (g : UnaryMap A A) (i : ι)
    (a value x : A i) (hxa : x ≠ a) :
    modifyUnary g i a value i x = g i x := by
  classical
  simp [modifyUnary, hxa]

@[simp] lemma modifyUnary_away (g : UnaryMap A A) (i j : ι)
    (hji : j ≠ i) (a value : A i) (x : A j) :
    modifyUnary g i a value j x = g j x := by
  classical
  simp [modifyUnary, hji]

/-- A pointwise modification remains a choice from the first sections. -/
lemma modifyUnary_choosesFirstSections
    {f : Operation 2 A A} {g : UnaryMap A A}
    (hg : ChoosesFirstSections f g)
    (i : ι) (a value : A i)
    (hvalue : ∃ b, f i (binaryPair a b) = value) :
    ChoosesFirstSections f (modifyUnary g i a value) := by
  classical
  intro j x
  by_cases hji : j = i
  · subst j
    by_cases hxa : x = a
    · subst x
      simpa using hvalue
    · rcases hg i x with ⟨b, hb⟩
      exact ⟨b, by simpa [hxa] using hb⟩
  · rcases hg j x with ⟨b, hb⟩
    exact ⟨b, by simpa [modifyUnary, hji] using hb⟩

/--
Two forced selections which differ only in one component must agree, by
synchrony and the existence of another coordinate.
-/
lemma forced_selections_agree
    (hunary : BoxTrivialAtArity P Q Φ 1)
    (hsync : IsSynchronous Φ)
    (hι : HasAtLeastTwo ι)
    {f : Operation 2 A A}
    (hsections : ∀ x ∈ P, UnaryIsBox Q (firstSection f x))
    {ω α : Tuple A} (hωQ : ω ∉ Q)
    {g : UnaryMap A A}
    (hg : ChoosesFirstSections f g)
    (hgω : ∀ i, g i (α i) = ω i)
    (i : ι) (a : A i) (hai : a ≠ α i)
    (v w : A i)
    (hv : ∃ b, f i (binaryPair a b) = v)
    (hw : ∃ b, f i (binaryPair a b) = w) :
    v = w := by
  classical
  let gv : UnaryMap A A := modifyUnary g i a v
  let gw : UnaryMap A A := modifyUnary g i a w
  have hgvchoose : ChoosesFirstSections f gv :=
    modifyUnary_choosesFirstSections hg i a v hv
  have hgwchoose : ChoosesFirstSections f gw :=
    modifyUnary_choosesFirstSections hg i a w hw
  have hgvω : ∀ j, gv j (α j) = ω j := by
    intro j
    by_cases hji : j = i
    · subst j
      change modifyUnary g i a v i (α i) = ω i
      rw [modifyUnary_at_ne _ _ _ _ _ (Ne.symm hai)]
      exact hgω i
    · simpa [gv, modifyUnary, hji] using hgω j
  have hgwω : ∀ j, gw j (α j) = ω j := by
    intro j
    by_cases hji : j = i
    · subst j
      change modifyUnary g i a w i (α i) = ω i
      rw [modifyUnary_at_ne _ _ _ _ _ (Ne.symm hai)]
      exact hgω i
    · simpa [gw, modifyUnary, hji] using hgω j
  have hgvmem : gv ∈ Φ :=
    firstSection_selection_mem hunary hsections hωQ hgvchoose hgvω
  have hgwmem : gw ∈ Φ :=
    firstSection_selection_mem hunary hsections hωQ hgwchoose hgwω
  rcases exists_ne_of_hasAtLeastTwo hι i with ⟨j, hji⟩
  have hcoord : gv j = gw j := by
    funext x
    simp [gv, gw, hji]
  have hmaps : gv = gw := hsync gv hgvmem gw hgwmem j hcoord
  have hat := congrFun (congrFun hmaps i) a
  simpa [gv, gw] using hat

/--
All first sections away from the distinguished witness input are constant.
This is the central synchrony conclusion in the all-box-sections lemma.
-/
lemma firstSections_constant_away
    (hunary : BoxTrivialAtArity P Q Φ 1)
    (hsync : IsSynchronous Φ)
    (hι : HasAtLeastTwo ι)
    {f : Operation 2 A A}
    (hsections : ∀ x ∈ P, UnaryIsBox Q (firstSection f x))
    {ω α : Tuple A} (hωQ : ω ∉ Q)
    {g : UnaryMap A A}
    (hg : ChoosesFirstSections f g)
    (hgω : ∀ i, g i (α i) = ω i) :
    ∀ i a, a ≠ α i → ∀ b c,
      f i (binaryPair a b) = f i (binaryPair a c) := by
  intro i a hai b c
  exact forced_selections_agree hunary hsync hι hsections hωQ hg hgω
    i a hai
    (f i (binaryPair a b)) (f i (binaryPair a c))
    ⟨b, rfl⟩ ⟨c, rfl⟩

/--
The common setup extracted from a non-box binary operation whose first
sections are all boxes: a forbidden image tuple, a forced selection belonging
to `Φ`, and constancy of every section away from the distinguished inputs.
-/
lemma allBoxSections_setup
    (hA : ∀ i, HasAtLeastTwo (A i))
    (hunary : BoxTrivialAtArity P Q Φ 1)
    (hsync : IsSynchronous Φ)
    (hι : HasAtLeastTwo ι)
    {f : Operation 2 A A}
    (hsections : ∀ x ∈ P, UnaryIsBox Q (firstSection f x))
    (hnbox : ¬ IsBox Q f) :
    ∃ ω : Tuple A, ω ∉ Q ∧
      ∃ α : Tuple A, ∃ g : UnaryMap A A,
        ChoosesFirstSections f g ∧
        (∀ i, g i (α i) = ω i) ∧
        g ∈ Φ ∧
        ∀ i a, a ≠ α i → ∀ b c,
          f i (binaryPair a b) = f i (binaryPair a c) := by
  rcases exists_image_witness_of_not_box hnbox with ⟨ω, hωQ, hωimage⟩
  rcases exists_firstSection_selection hA hωimage with
    ⟨α, g, hg, hgω⟩
  have hgmem : g ∈ Φ :=
    firstSection_selection_mem hunary hsections hωQ hg hgω
  have hconstant :=
    firstSections_constant_away hunary hsync hι hsections hωQ hg hgω
  exact ⟨ω, hωQ, α, g, hg, hgω, hgmem, hconstant⟩

/--
If every first section, including the distinguished ones, is constant, then
the binary operation depends only on its first input and is a dictator.
-/
lemma dictator_of_firstSections_constant
    (hunary : BoxTrivialAtArity P Q Φ 1)
    {f : Operation 2 A A} (hf : Preserves P Q f)
    {x : Tuple A} (hx : x ∈ P)
    {ω α : Tuple A} (hωQ : ω ∉ Q)
    (hωsection : ∀ i, ∃ b, f i (binaryPair (α i) b) = ω i)
    (hconstant : ∀ i a b c,
      f i (binaryPair a b) = f i (binaryPair a c)) :
    IsDictator Φ f := by
  rcases secondSection_classification hunary hf hx with hmem | hbox
  · refine ⟨0, secondSection f x, hmem, ?_⟩
    intro i input
    rw [← binaryPair_eta input]
    exact hconstant i (input 0) (input 1) (x i)
  · exact False.elim (hωQ (hbox (fun i ↦ by
      rcases hωsection i with ⟨b, hb⟩
      exact ⟨α i, by
        change f i (binaryPair (α i) (x i)) = ω i
        exact (hconstant i (α i) (x i) b).trans hb⟩)))

/--
Full projections and a proper promise force the relation to have at least two
coordinates. This is used whenever synchrony is tested away from one chosen
coordinate.
-/
lemma index_hasAtLeastTwo
    [Nonempty ι]
    (hPQ : P ⊆ Q)
    (hproper : ∃ z : Tuple A, z ∉ Q)
    (hfull : HasFullProjections P) :
    HasAtLeastTwo ι := by
  classical
  by_contra hnot
  have hall : ∀ i j : ι, i = j := by
    intro i j
    by_contra hij
    exact hnot ⟨i, j, hij⟩
  rcases hproper with ⟨z, hz⟩
  let i₀ : ι := Classical.choice inferInstance
  rcases hfull i₀ (z i₀) with ⟨x, hxP, hxi⟩
  have hxz : x = z := by
    funext i
    have hii : i = i₀ := hall i i₀
    subst i
    exact hxi
  exact hz (hxz ▸ hPQ hxP)

/-- The identity unary map. -/
def identityUnary : UnaryMap A A :=
  fun _ a ↦ a

/-- Inclusion `P ⊆ Q` makes the identity map a unary polymorphism. -/
lemma identityUnary_isUnaryPolymorphism
    (hPQ : P ⊆ Q) :
    IsUnaryPolymorphism P Q (identityUnary (A := A)) := by
  intro x hx
  simpa [identityUnary] using hPQ hx

/-- Under unary box-triviality and properness, the identity tuple belongs to `Φ`. -/
lemma identityUnary_mem
    (hunary : BoxTrivialAtArity P Q Φ 1)
    (hPQ : P ⊆ Q)
    (hproper : ∃ z : Tuple A, z ∉ Q) :
    identityUnary (A := A) ∈ Φ := by
  rcases unary_classification hunary
      (identityUnary_isUnaryPolymorphism hPQ) with hmem | hbox
  · exact hmem
  · rcases hproper with ⟨z, hz⟩
    apply False.elim (hz (hbox ?_))
    intro i
    exact ⟨z i, rfl⟩

/--
If an at-least-two-element type is not a two-element type, then two distinct
elements can be found away from any prescribed element.
-/
lemma exists_two_away_of_not_exactlyTwo
    {α : Type uA} (hα : HasAtLeastTwo α) (ω : α)
    (hnot : ¬ HasExactlyTwo α) :
    ∃ a b, a ≠ ω ∧ b ≠ ω ∧ a ≠ b := by
  by_contra hnone
  have hallAway : ∀ a, a ≠ ω → ∀ b, b ≠ ω → a = b := by
    intro a ha b hb
    by_contra hab
    exact hnone ⟨a, b, ha, hb, hab⟩
  rcases exists_ne_of_hasAtLeastTwo hα ω with ⟨p, hpω⟩
  apply hnot
  refine ⟨ω, p, Ne.symm hpω, ?_⟩
  intro x
  by_cases hxω : x = ω
  · exact Or.inl hxω
  · exact Or.inr (hallAway x hxω p hpω)

/-- The transposition of two specified values. -/
noncomputable def swapValues {α : Type uA} (a b : α) : α → α := by
  classical
  exact fun x ↦ if x = a then b else if x = b then a else x

@[simp] lemma swapValues_left {α : Type uA} (a b : α) :
    swapValues a b a = b := by
  classical
  simp [swapValues]

@[simp] lemma swapValues_right {α : Type uA} (a b : α) :
    swapValues a b b = a := by
  classical
  by_cases hba : b = a
  · subst b
    simp [swapValues]
  · simp [swapValues, hba]

@[simp] lemma swapValues_away {α : Type uA} {a b x : α}
    (hxa : x ≠ a) (hxb : x ≠ b) :
    swapValues a b x = x := by
  classical
  simp [swapValues, hxa, hxb]

lemma swapValues_involutive {α : Type uA} (a b : α) :
    Function.LeftInverse (swapValues a b) (swapValues a b) := by
  intro x
  by_cases hxa : x = a
  · subst x
    simp
  · by_cases hxb : x = b
    · subst x
      simp
    · simp [hxa, hxb]

lemma swapValues_surjective {α : Type uA} (a b : α) :
    Function.Surjective (swapValues a b) :=
  (swapValues_involutive a b).surjective

/-- Apply one transposition in one coordinate and the identity elsewhere. -/
noncomputable def singleCoordinateSwap (i : ι) (a b : A i) :
    UnaryMap A A := by
  classical
  intro j
  by_cases hji : j = i
  · subst j
    exact swapValues a b
  · exact fun x ↦ x

@[simp] lemma singleCoordinateSwap_at (i : ι) (a b : A i) :
    singleCoordinateSwap i a b i = swapValues a b := by
  classical
  simp [singleCoordinateSwap]

@[simp] lemma singleCoordinateSwap_away (i j : ι) (hji : j ≠ i)
    (a b : A i) :
    singleCoordinateSwap i a b j = identityUnary (A := A) j := by
  classical
  change singleCoordinateSwap i a b j = (fun x ↦ x)
  simp [singleCoordinateSwap, hji]

/-- Every component of a single-coordinate transposition is surjective. -/
lemma singleCoordinateSwap_surjective
    (i : ι) (a b : A i) :
    ∀ j, Function.Surjective (singleCoordinateSwap i a b j) := by
  intro j
  by_cases hji : j = i
  · subst j
    simpa using swapValues_surjective a b
  · rw [singleCoordinateSwap_away i j hji]
    exact Function.surjective_id

/--
Synchrony forbids a nontrivial unary permutation which changes only one
coordinate. The hypotheses are phrased so the lemma can be reused with the
transpositions constructed in both hard cases of the proof.
-/
lemma no_nontrivial_single_coordinate_permutation
    (hunary : BoxTrivialAtArity P Q Φ 1)
    (hPQ : P ⊆ Q)
    (hproper : ∃ z : Tuple A, z ∉ Q)
    (hperm : IsPermutationFamily Φ)
    (hsync : IsSynchronous Φ)
    (hι : HasAtLeastTwo ι)
    {i : ι} {ψ : UnaryMap A A}
    (hψpoly : IsUnaryPolymorphism P Q ψ)
    (hψsurj : ∀ j, Function.Surjective (ψ j))
    (haway : ∀ j, j ≠ i → ψ j = identityUnary (A := A) j)
    (hne : ψ i ≠ identityUnary (A := A) i) :
    False := by
  have hidmem : identityUnary (A := A) ∈ Φ :=
    identityUnary_mem hunary hPQ hproper
  have hψnbox : ¬ UnaryIsBox Q ψ := by
    intro hbox
    rcases hproper with ⟨z, hz⟩
    apply hz
    apply hbox
    intro j
    rcases hψsurj j (z j) with ⟨a, ha⟩
    exact ⟨a, ha⟩
  have hψmem : ψ ∈ Φ :=
    (unary_mem_iff_not_box hunary hperm hproper hψpoly).2 hψnbox
  rcases exists_ne_of_hasAtLeastTwo hι i with ⟨j, hji⟩
  have hψid : ψ = identityUnary (A := A) :=
    hsync ψ hψmem (identityUnary (A := A)) hidmem j (haway j hji)
  exact hne (congrFun hψid i)

/--
In the separated situation, unary box-triviality and synchrony force every
alphabet to be Boolean.
-/
lemma all_alphabets_boolean_of_separated
    [Nonempty ι]
    (hA : ∀ i, HasAtLeastTwo (A i))
    (hPQ : P ⊆ Q)
    (hproper : ∃ z : Tuple A, z ∉ Q)
    (hfull : HasFullProjections P)
    (hseparate : ∀ {z w : Tuple A}, z ∈ P → w ∈ P →
      ∀ i, z i = w i → z = w)
    (hunary : BoxTrivialAtArity P Q Φ 1)
    (hperm : IsPermutationFamily Φ)
    (hsync : IsSynchronous Φ) :
    ∀ i, HasExactlyTwo (A i) := by
  classical
  have hι : HasAtLeastTwo ι :=
    index_hasAtLeastTwo hPQ hproper hfull
  let k : ι := Classical.choice inferInstance
  let a : A k := Classical.choose (hA k)
  let y : Tuple A := completion hfull hseparate k a
  let b : A k := Classical.choose (exists_ne_of_hasAtLeastTwo (hA k) (y k))
  let ybar : Tuple A := completion hfull hseparate k b
  have hyP : y ∈ P := completion_mem hfull hseparate k a
  have hybarP : ybar ∈ P := completion_mem hfull hseparate k b
  have hbne : b ≠ y k :=
    Classical.choose_spec (exists_ne_of_hasAtLeastTwo (hA k) (y k))
  have hybar_ne_y : ybar ≠ y := by
    intro heq
    have hk := congrFun heq k
    have hybark : ybar k = b :=
      completion_at hfull hseparate k b
    exact hbne (hybark.symm.trans hk)
  have hdiff : ∀ i, ybar i ≠ y i := by
    intro i hi
    exact hybar_ne_y (hseparate hybarP hyP i hi)
  let g : UnaryMap A A := fun i t ↦
    if t = y i then ybar i else t
  have hgpoly : IsUnaryPolymorphism P Q g := by
    intro x hx
    by_cases hxy : x = y
    · subst x
      have hout : (fun i ↦ g i (y i)) = ybar := by
        funext i
        simp [g]
      rw [hout]
      exact hPQ hybarP
    · have haway : ∀ i, x i ≠ y i := by
        intro i hxi
        exact hxy (hseparate hx hyP i hxi)
      have hout : (fun i ↦ g i (x i)) = x := by
        funext i
        simp [g, haway i]
      rw [hout]
      exact hPQ hx
  have hgnotmem : g ∉ Φ := by
    intro hgmem
    have heq : g k (y k) = g k (ybar k) := by
      simp [g]
    have := (hperm g hgmem k).1 heq
    exact hdiff k this.symm
  have hgbox : UnaryIsBox Q g := by
    rcases unary_classification hunary hgpoly with hmem | hbox
    · exact False.elim (hgnotmem hmem)
    · exact hbox
  have hallQ : ∀ z : Tuple A, (∀ i, z i ≠ y i) → z ∈ Q := by
    intro z hz
    apply hgbox
    intro i
    exact ⟨z i, by simp [g, hz i]⟩
  intro i
  by_contra hnotTwo
  rcases exists_two_away_of_not_exactlyTwo (hA i) (y i) hnotTwo with
    ⟨p, q, hpy, hqy, hpq⟩
  let ψ : UnaryMap A A := singleCoordinateSwap i p q
  have hψpoly : IsUnaryPolymorphism P Q ψ := by
    intro x hx
    by_cases hxy : x = y
    · subst x
      have hout : (fun j ↦ ψ j (y j)) = y := by
        funext j
        by_cases hji : j = i
        · subst j
          rw [show ψ i = swapValues p q by simp [ψ]]
          exact swapValues_away (Ne.symm hpy) (Ne.symm hqy)
        · simp [ψ, hji, identityUnary]
      rw [hout]
      exact hPQ hyP
    · apply hallQ
      intro j
      have hxjy : x j ≠ y j := by
        intro hxj
        exact hxy (hseparate hx hyP j hxj)
      by_cases hji : j = i
      · subst j
        rw [show ψ i = swapValues p q by simp [ψ]]
        by_cases hxp : x i = p
        · rw [hxp]
          simpa using hqy
        · by_cases hxq : x i = q
          · rw [hxq]
            simpa using hpy
          · simpa [swapValues_away hxp hxq] using hxjy
      · simpa [ψ, hji, identityUnary] using hxjy
  have hψsurj : ∀ j, Function.Surjective (ψ j) :=
    singleCoordinateSwap_surjective i p q
  have hψaway : ∀ j, j ≠ i →
      ψ j = identityUnary (A := A) j := by
    intro j hji
    exact singleCoordinateSwap_away i j hji p q
  have hψne : ψ i ≠ identityUnary (A := A) i := by
    intro heq
    have hat := congrFun heq p
    have hqp : q = p := by simpa [ψ, identityUnary] using hat
    exact hpq hqp.symm
  exact no_nontrivial_single_coordinate_permutation
    hunary hPQ hproper hperm hsync hι hψpoly hψsurj hψaway hψne

/--
A nonconstant distinguished section in the all-box setup produces a unit
witness. If its alphabet had a third value, a transposition away from `ω`
would contradict synchrony.
-/
lemma unitWitness_of_distinguishedSection_nonconstant
    (hA : ∀ i, HasAtLeastTwo (A i))
    (hunary : BoxTrivialAtArity P Q Φ 1)
    (hPQ : P ⊆ Q)
    (hproper : ∃ z : Tuple A, z ∉ Q)
    (hperm : IsPermutationFamily Φ)
    (hsync : IsSynchronous Φ)
    (hι : HasAtLeastTwo ι)
    {f : Operation 2 A A}
    (hsections : ∀ x ∈ P, UnaryIsBox Q (firstSection f x))
    {ω α : Tuple A}
    {g : UnaryMap A A}
    (hg : ChoosesFirstSections f g)
    (hgω : ∀ i, g i (α i) = ω i)
    (hgmem : g ∈ Φ)
    (hnonconstant : ∃ i, ∃ b c,
      f i (binaryPair (α i) b) ≠ f i (binaryPair (α i) c)) :
    HasUnitWitness Q := by
  classical
  rcases hnonconstant with ⟨i, b, c, hbc⟩
  obtain ⟨v, e, he, hvω⟩ :
      ∃ v : A i, ∃ e : A i,
        f i (binaryPair (α i) e) = v ∧ v ≠ ω i := by
    by_cases hbω : f i (binaryPair (α i) b) = ω i
    · refine ⟨f i (binaryPair (α i) c), c, rfl, ?_⟩
      intro hcω
      exact hbc (hbω.trans hcω.symm)
    · exact ⟨f i (binaryPair (α i) b), b, rfl, hbω⟩
  let g' : UnaryMap A A := modifyUnary g i (α i) v
  have hg'choose : ChoosesFirstSections f g' :=
    modifyUnary_choosesFirstSections hg i (α i) v ⟨e, he⟩
  have hg'poly : IsUnaryPolymorphism P Q g' :=
    choosingFirstSections_isUnaryPolymorphism hsections hg'choose
  have hg'notmem : g' ∉ Φ := by
    intro hg'mem
    rcases (hperm g hgmem i).2 v with ⟨a, ha⟩
    have haα : a ≠ α i := by
      intro haeq
      subst a
      exact hvω ((hgω i).symm.trans ha).symm
    have hsame : g' i a = g' i (α i) := by
      change modifyUnary g i (α i) v i a =
        modifyUnary g i (α i) v i (α i)
      rw [modifyUnary_at_ne _ _ _ _ _ haα, modifyUnary_at_eq]
      exact ha
    have := (hperm g' hg'mem i).1 hsame
    exact haα this
  have hg'box : UnaryIsBox Q g' := by
    rcases unary_classification hunary hg'poly with hmem | hbox
    · exact False.elim (hg'notmem hmem)
    · exact hbox
  have hallQ : ∀ y : Tuple A, y i ≠ ω i → y ∈ Q := by
    intro y hyω
    apply hg'box
    intro j
    by_cases hji : j = i
    · subst j
      rcases (hperm g hgmem i).2 (y i) with ⟨a, ha⟩
      have haα : a ≠ α i := by
        intro haeq
        subst a
        exact hyω ((hgω i).symm.trans ha).symm
      exact ⟨a, by
        change modifyUnary g i (α i) v i a = y i
        rw [modifyUnary_at_ne _ _ _ _ _ haα]
        exact ha⟩
    · rcases (hperm g hgmem j).2 (y j) with ⟨a, ha⟩
      exact ⟨a, by
        change modifyUnary g i (α i) v j a = y j
        rw [modifyUnary_away _ _ _ hji]
        exact ha⟩
  have htwo : HasExactlyTwo (A i) := by
    by_contra hnotTwo
    rcases exists_two_away_of_not_exactlyTwo (hA i) (ω i) hnotTwo with
      ⟨a, b, haω, hbω, hab⟩
    let ψ : UnaryMap A A := singleCoordinateSwap i a b
    have hψpoly : IsUnaryPolymorphism P Q ψ := by
      intro x hx
      by_cases hxi : x i = ω i
      · have hψx : (fun j ↦ ψ j (x j)) = x := by
          funext j
          by_cases hji : j = i
          · subst j
            rw [show ψ i = swapValues a b by simp [ψ]]
            apply swapValues_away
            · intro hxia
              exact haω (hxia ▸ hxi)
            · intro hxib
              exact hbω (hxib ▸ hxi)
          · simp [ψ, hji, identityUnary]
        rw [hψx]
        exact hPQ hx
      · apply hallQ
        rw [show ψ i = swapValues a b by simp [ψ]]
        by_cases hxia : x i = a
        · rw [hxia]
          simpa using hbω
        · by_cases hxib : x i = b
          · rw [hxib]
            simpa using haω
          · simpa [swapValues_away hxia hxib] using hxi
    have hψsurj : ∀ j, Function.Surjective (ψ j) :=
      singleCoordinateSwap_surjective i a b
    have hψaway : ∀ j, j ≠ i →
        ψ j = identityUnary (A := A) j := by
      intro j hji
      exact singleCoordinateSwap_away i j hji a b
    have hψne : ψ i ≠ identityUnary (A := A) i := by
      intro heq
      have hat := congrFun heq a
      have hba : b = a := by simpa [ψ, identityUnary] using hat
      exact hab hba.symm
    exact no_nontrivial_single_coordinate_permutation
      hunary hPQ hproper hperm hsync hι hψpoly hψsurj hψaway hψne
  exact ⟨i, v, htwo, fun y hyv ↦ hallQ y (by simpa [hyv] using hvω)⟩

/--
The all-box-sections lemma from the proof of Theorem 1.4.

If every first-input section over `P` has unary box type, then the binary
operation is already box-trivial, unless `Q` has a unit-witness obstruction.
-/
lemma allBoxSections
    [Nonempty ι]
    (hA : ∀ i, HasAtLeastTwo (A i))
    (hunary : BoxTrivialAtArity P Q Φ 1)
    (hPQ : P ⊆ Q)
    (hproper : ∃ z : Tuple A, z ∉ Q)
    (hfull : HasFullProjections P)
    (hperm : IsPermutationFamily Φ)
    (hsync : IsSynchronous Φ)
    {f : Operation 2 A A} (hf : Preserves P Q f)
    (hsections : ∀ x ∈ P, UnaryIsBox Q (firstSection f x)) :
    IsBoxTrivial Q Φ f ∨ HasUnitWitness Q := by
  classical
  by_cases hbox : IsBox Q f
  · exact Or.inl (Or.inr hbox)
  have hι : HasAtLeastTwo ι :=
    index_hasAtLeastTwo hPQ hproper hfull
  rcases allBoxSections_setup hA hunary hsync hι hsections hbox with
    ⟨ω, hωQ, α, g, hg, hgω, hgmem, hconstantAway⟩
  by_cases hconstantAt : ∀ i b c,
      f i (binaryPair (α i) b) = f i (binaryPair (α i) c)
  · let i₀ : ι := Classical.choice inferInstance
    let a : A i₀ := Classical.choose (hA i₀)
    rcases hfull i₀ a with ⟨x, hx, _⟩
    have hωsection : ∀ i, ∃ b,
        f i (binaryPair (α i) b) = ω i := by
      intro i
      rcases hg i (α i) with ⟨b, hb⟩
      exact ⟨b, hb.trans (hgω i)⟩
    have hconstant : ∀ i a b c,
        f i (binaryPair a b) = f i (binaryPair a c) := by
      intro i a b c
      by_cases ha : a = α i
      · subst a
        exact hconstantAt i b c
      · exact hconstantAway i a ha b c
    exact Or.inl (Or.inl
      (dictator_of_firstSections_constant
        hunary hf hx hωQ hωsection hconstant))
  · have hnonconstant : ∃ i, ∃ b c,
        f i (binaryPair (α i) b) ≠
          f i (binaryPair (α i) c) := by
      by_contra hnone
      apply hconstantAt
      intro i b c
      by_contra hne
      exact hnone ⟨i, b, c, hne⟩
    exact Or.inr
      (unitWitness_of_distinguishedSection_nonconstant
        hA hunary hPQ hproper hperm hsync hι hsections
        hg hgω hgmem hnonconstant)

/--
Any non-box-trivial binary polymorphism has a second section in `Φ`, provided
there is no unit witness. This is the transposed all-box lemma.
-/
lemma exists_secondSection_mem_of_not_boxTrivial
    [Nonempty ι]
    (hA : ∀ i, HasAtLeastTwo (A i))
    (hunary : BoxTrivialAtArity P Q Φ 1)
    (hPQ : P ⊆ Q)
    (hproper : ∃ z : Tuple A, z ∉ Q)
    (hfull : HasFullProjections P)
    (hperm : IsPermutationFamily Φ)
    (hsync : IsSynchronous Φ)
    {h : Operation 2 A A} (hh : Preserves P Q h)
    (hnottrivial : ¬ IsBoxTrivial Q Φ h)
    (hnoUnit : ¬ HasUnitWitness Q) :
    ∃ y ∈ P, secondSection h y ∈ Φ := by
  by_contra hnone
  have hallSecondBox : ∀ x ∈ P,
      UnaryIsBox Q (secondSection h x) := by
    intro x hx
    rcases secondSection_classification hunary hh hx with hmem | hbox
    · exact False.elim (hnone ⟨x, hx, hmem⟩)
    · exact hbox
  have hallFirstTranspose : ∀ x ∈ P,
      UnaryIsBox Q (firstSection (transposeBinary h) x) := by
    intro x hx
    rw [firstSection_transposeBinary]
    exact hallSecondBox x hx
  rcases allBoxSections hA hunary hPQ hproper hfull hperm hsync
      (transposeBinary_preserves hh) hallFirstTranspose with
    htrivial | hunit
  · exact hnottrivial ((transposeBinary_isBoxTrivial_iff).1 htrivial)
  · exact hnoUnit hunit

/--
In the mixed non-box case, and in the absence of a unit witness, some second
section of the normalized operation belongs to `Φ`. This is the distinguished
tuple `y` used in both remaining branches of the proof.
-/
lemma exists_normalized_secondSection_mem
    [Nonempty ι]
    (hA : ∀ i, HasAtLeastTwo (A i))
    (hunary : BoxTrivialAtArity P Q Φ 1)
    (hPQ : P ⊆ Q)
    (hproper : ∃ z : Tuple A, z ∉ Q)
    (hfull : HasFullProjections P)
    (hperm : IsPermutationFamily Φ)
    (hsync : IsSynchronous Φ)
    {f : Operation 2 A A} (hf : Preserves P Q f)
    {σ τ : Tuple A}
    (hσbox : UnaryIsBox Q (firstSection f σ))
    (hτmem : firstSection f τ ∈ Φ)
    (hfnotbox : ¬ IsBox Q f)
    (hnoUnit : ¬ HasUnitWitness Q) :
    ∃ y ∈ P, secondSection (normalizeFirstSections f) y ∈ Φ := by
  have hnorm :
      Preserves P Q (normalizeFirstSections f) :=
    normalizeFirstSections_preserves hunary hPQ hperm hf
  have hnormNotTrivial :
      ¬ IsBoxTrivial Q Φ (normalizeFirstSections f) :=
    mixedNormalization_not_boxTrivial
      hA hunary hPQ hproper hperm hf hσbox hτmem hfnotbox
  by_contra hnone
  have hallSecondBox : ∀ x ∈ P,
      UnaryIsBox Q (secondSection (normalizeFirstSections f) x) := by
    intro x hx
    rcases secondSection_classification hunary hnorm hx with hmem | hbox
    · exact False.elim (hnone ⟨x, hx, hmem⟩)
    · exact hbox
  have hallFirstTranspose : ∀ x ∈ P,
      UnaryIsBox Q
        (firstSection (transposeBinary (normalizeFirstSections f)) x) := by
    intro x hx
    rw [firstSection_transposeBinary]
    exact hallSecondBox x hx
  rcases allBoxSections hA hunary hPQ hproper hfull hperm hsync
      (transposeBinary_preserves hnorm) hallFirstTranspose with
    htrivial | hunit
  · exact hnormNotTrivial
      ((transposeBinary_isBoxTrivial_iff).1 htrivial)
  · exact hnoUnit hunit

/--
Once a normalized second section belongs to `Φ`, a permutation-valued first
section can occur only at the distinguished tuple `τ`.
-/
lemma permutation_input_eq_of_normalized_secondSection_mem
    (hperm : IsPermutationFamily Φ)
    {f : Operation 2 A A} {τ y : Tuple A}
    (hτmem : firstSection f τ ∈ Φ)
    (hymem : secondSection (normalizeFirstSections f) y ∈ Φ) :
    ∀ i a, FirstSectionIsPermutation f i a → a = τ i := by
  have hτperm : ∀ i, FirstSectionIsPermutation f i (τ i) := by
    intro i
    exact hperm (firstSection f τ) hτmem i
  intro i a ha
  apply (hperm
    (secondSection (normalizeFirstSections f) y) hymem i).1
  change normalizeFirstSections f i (binaryPair a (y i)) =
    normalizeFirstSections f i (binaryPair (τ i) (y i))
  rw [normalizeFirstSections_of_permutation f i a (y i) ha,
    normalizeFirstSections_of_permutation
      f i (τ i) (y i) (hτperm i)]

/--
Every normalized first section over a member of `P` other than `τ` has box
type.
-/
lemma normalized_firstSection_box_of_ne
    (hunary : BoxTrivialAtArity P Q Φ 1)
    (hperm : IsPermutationFamily Φ)
    {f : Operation 2 A A} (hf : Preserves P Q f)
    {τ y x : Tuple A}
    (hτmem : firstSection f τ ∈ Φ)
    (hymem : secondSection (normalizeFirstSections f) y ∈ Φ)
    (hx : x ∈ P) (hxτ : x ≠ τ) :
    UnaryIsBox Q (firstSection (normalizeFirstSections f) x) := by
  rcases firstSection_classification hunary hf hx with hmem | hbox
  · apply False.elim
    apply hxτ
    funext i
    exact permutation_input_eq_of_normalized_secondSection_mem
      hperm hτmem hymem i (x i) (hperm (firstSection f x) hmem i)
  · intro z hz
    apply hbox
    intro i
    rcases hz i with ⟨b, hb⟩
    rcases (normalized_firstSection_image_iff i (x i) (z i)).1
      ⟨b, by simpa [firstSection] using hb⟩ with ⟨a, ha⟩
    exact ⟨a, by simpa [firstSection] using ha⟩

/--
The closure property around the distinguished tuple in the mixed-section
argument.
-/
def HasMixedClosure (P Q : Relation A) (y : Tuple A) : Prop :=
  ∀ z ∈ P, z ≠ y →
    ∀ w : Tuple A, (∀ i, z i ≠ y i → w i ≠ y i) → w ∈ Q

/-- The modified second-section map used to prove mixed closure. -/
noncomputable def mixedClosureMap
    (h : Operation 2 A A) (τ y z : Tuple A) : UnaryMap A A := by
  classical
  exact fun i a ↦ if a = τ i then z i else h i (binaryPair a (y i))

/--
Abstract core of the mixed closure argument. The first section at `τ` is the
identity, all other `P`-sections are boxes, and the second section at `y` is a
member of the permutation family.
-/
lemma hasMixedClosure_of_section_data
    (hunary : BoxTrivialAtArity P Q Φ 1)
    (hPQ : P ⊆ Q)
    (hperm : IsPermutationFamily Φ)
    {h : Operation 2 A A} {τ y : Tuple A}
    (hτid : firstSection h τ = (fun _ a ↦ a))
    (hymem : secondSection h y ∈ Φ)
    (hallbox : ∀ x ∈ P, x ≠ τ →
      UnaryIsBox Q (firstSection h x)) :
    HasMixedClosure P Q y := by
  classical
  intro z hzP hzy
  let η : UnaryMap A A := mixedClosureMap h τ y z
  have hηpoly : IsUnaryPolymorphism P Q η := by
    intro x hxP
    by_cases hxτ : x = τ
    · subst x
      have hout : (fun i ↦ η i (τ i)) = z := by
        funext i
        simp [η, mixedClosureMap]
      rw [hout]
      exact hPQ hzP
    · apply hallbox x hxP hxτ
      intro i
      by_cases hxi : x i = τ i
      · refine ⟨z i, ?_⟩
        change h i (binaryPair (x i) (z i)) = η i (x i)
        rw [hxi]
        change firstSection h τ i (z i) =
          mixedClosureMap h τ y z i (τ i)
        rw [hτid]
        simp [mixedClosureMap]
      · refine ⟨y i, ?_⟩
        change h i (binaryPair (x i) (y i)) = η i (x i)
        simp [η, mixedClosureMap, hxi]
  have hηnotmem : η ∉ Φ := by
    intro hηmem
    have hi : ∃ i, z i ≠ y i := by
      by_contra hnone
      apply hzy
      funext i
      by_contra hne
      exact hnone ⟨i, hne⟩
    rcases hi with ⟨i, hziy⟩
    rcases (hperm (secondSection h y) hymem i).2 (z i) with
      ⟨a, ha⟩
    have hτy : h i (binaryPair (τ i) (y i)) = y i := by
      change firstSection h τ i (y i) = y i
      rw [hτid]
    have haτ : a ≠ τ i := by
      intro haeq
      subst a
      exact hziy (ha.symm.trans hτy)
    have heq : η i a = η i (τ i) := by
      change mixedClosureMap h τ y z i a =
        mixedClosureMap h τ y z i (τ i)
      rw [show mixedClosureMap h τ y z i a =
          h i (binaryPair a (y i)) by simp [mixedClosureMap, haτ]]
      rw [show mixedClosureMap h τ y z i (τ i) = z i by
        simp [mixedClosureMap]]
      exact ha
    have := (hperm η hηmem i).1 heq
    exact haτ this
  have hηbox : UnaryIsBox Q η := by
    rcases unary_classification hunary hηpoly with hmem | hbox
    · exact False.elim (hηnotmem hmem)
    · exact hbox
  intro w hw
  apply hηbox
  intro i
  rcases (hperm (secondSection h y) hymem i).2 (w i) with
    ⟨a, ha⟩
  by_cases haτ : a = τ i
  · have hτy : h i (binaryPair (τ i) (y i)) = y i := by
      change firstSection h τ i (y i) = y i
      rw [hτid]
    have hwy : w i = y i := by
      subst a
      exact ha.symm.trans hτy
    have hziy : z i = y i := by
      by_contra hne
      exact hw i hne hwy
    exact ⟨τ i, by simp [η, mixedClosureMap, hziy, hwy]⟩
  · exact ⟨a, by
      change mixedClosureMap h τ y z i a = w i
      simpa [mixedClosureMap, haτ] using ha⟩

/-- The normalized mixed-section data therefore yields the desired closure. -/
lemma normalized_hasMixedClosure
    (hunary : BoxTrivialAtArity P Q Φ 1)
    (hPQ : P ⊆ Q)
    (hperm : IsPermutationFamily Φ)
    {f : Operation 2 A A} (hf : Preserves P Q f)
    {τ y : Tuple A}
    (hτmem : firstSection f τ ∈ Φ)
    (hymem : secondSection (normalizeFirstSections f) y ∈ Φ) :
    HasMixedClosure P Q y := by
  have hτperm : ∀ i, FirstSectionIsPermutation f i (τ i) := by
    intro i
    exact hperm (firstSection f τ) hτmem i
  apply hasMixedClosure_of_section_data hunary hPQ hperm
    (normalized_firstSection_eq_identity hτperm) hymem
  intro x hx hxτ
  exact normalized_firstSection_box_of_ne
    hunary hperm hf hτmem hymem hx hxτ

/--
The full first part of the mixed-section argument: in the non-box case and
without a unit witness, there is a distinguished `y ∈ P` with mixed closure.
-/
lemma exists_mixedClosure_base
    [Nonempty ι]
    (hA : ∀ i, HasAtLeastTwo (A i))
    (hunary : BoxTrivialAtArity P Q Φ 1)
    (hPQ : P ⊆ Q)
    (hproper : ∃ z : Tuple A, z ∉ Q)
    (hfull : HasFullProjections P)
    (hperm : IsPermutationFamily Φ)
    (hsync : IsSynchronous Φ)
    {f : Operation 2 A A} (hf : Preserves P Q f)
    {σ τ : Tuple A}
    (hσbox : UnaryIsBox Q (firstSection f σ))
    (hτmem : firstSection f τ ∈ Φ)
    (hfnotbox : ¬ IsBox Q f)
    (hnoUnit : ¬ HasUnitWitness Q) :
    ∃ y ∈ P, HasMixedClosure P Q y := by
  rcases exists_normalized_secondSection_mem
      hA hunary hPQ hproper hfull hperm hsync hf
      hσbox hτmem hfnotbox hnoUnit with
    ⟨y, hyP, hymem⟩
  exact ⟨y, hyP,
    normalized_hasMixedClosure hunary hPQ hperm hf hτmem hymem⟩

/-- The final unary map in the non-Boolean mixed branch. -/
noncomputable def mixedNonBooleanMap
    (y ω κ : Tuple A) : UnaryMap A A := by
  classical
  exact fun i a ↦
    if a = y i then y i else if y i = ω i then κ i else ω i

/--
Mixed closure is incompatible with a non-Boolean alphabet under unary
box-triviality: the map `χ` is a polymorphism but is neither a permutation
tuple nor box type.
-/
lemma false_of_mixedClosure_nonBoolean
    (hA : ∀ i, HasAtLeastTwo (A i))
    (hunary : BoxTrivialAtArity P Q Φ 1)
    (hPQ : P ⊆ Q)
    (hperm : IsPermutationFamily Φ)
    {y : Tuple A} (hyP : y ∈ P)
    (hclosure : HasMixedClosure P Q y)
    (hnonBoolean : ∃ i, ¬ HasExactlyTwo (A i))
    {ω : Tuple A} (hωQ : ω ∉ Q) :
    False := by
  classical
  let κ : Tuple A := fun i ↦
    Classical.choose (exists_ne_of_hasAtLeastTwo (hA i) (ω i))
  have hκω : ∀ i, κ i ≠ ω i := by
    intro i
    exact Classical.choose_spec
      (exists_ne_of_hasAtLeastTwo (hA i) (ω i))
  let χ : UnaryMap A A := mixedNonBooleanMap y ω κ
  have hχpoly : IsUnaryPolymorphism P Q χ := by
    intro z hzP
    by_cases hzy : z = y
    · subst z
      have hout : (fun i ↦ χ i (y i)) = y := by
        funext i
        simp [χ, mixedNonBooleanMap]
      rw [hout]
      exact hPQ hyP
    · apply hclosure z hzP hzy
      intro i hziy
      change mixedNonBooleanMap y ω κ i (z i) ≠ y i
      by_cases hyω : y i = ω i
      · have hziω : z i ≠ ω i :=
          fun h ↦ hziy (h.trans hyω.symm)
        simp [mixedNonBooleanMap, hyω, hziω, hκω i]
      · simp [mixedNonBooleanMap, hziy, hyω, Ne.symm hyω]
  have hχnotmem : χ ∉ Φ := by
    intro hχmem
    rcases hnonBoolean with ⟨i, hnotTwo⟩
    rcases exists_two_away_of_not_exactlyTwo (hA i) (y i) hnotTwo with
      ⟨a, b, hay, hby, hab⟩
    have heq : χ i a = χ i b := by
      simp [χ, mixedNonBooleanMap, hay, hby]
    have := (hperm χ hχmem i).1 heq
    exact hab this
  have hωimage : ∀ i, ∃ a, χ i a = ω i := by
    intro i
    by_cases hyω : y i = ω i
    · exact ⟨y i, by simp [χ, mixedNonBooleanMap, hyω]⟩
    · rcases exists_ne_of_hasAtLeastTwo (hA i) (y i) with ⟨a, hay⟩
      exact ⟨a, by simp [χ, mixedNonBooleanMap, hay, hyω]⟩
  rcases unary_classification hunary hχpoly with hmem | hbox
  · exact hχnotmem hmem
  · exact hωQ (hbox hωimage)

/--
The non-Boolean mixed-section lemma from the proof of Theorem 1.4.
-/
lemma mixedSections_nonBoolean
    [Nonempty ι]
    (hA : ∀ i, HasAtLeastTwo (A i))
    (hunary : BoxTrivialAtArity P Q Φ 1)
    (hPQ : P ⊆ Q)
    (hproper : ∃ z : Tuple A, z ∉ Q)
    (hfull : HasFullProjections P)
    (hperm : IsPermutationFamily Φ)
    (hsync : IsSynchronous Φ)
    {f : Operation 2 A A} (hf : Preserves P Q f)
    {σ τ : Tuple A}
    (hσbox : UnaryIsBox Q (firstSection f σ))
    (hτmem : firstSection f τ ∈ Φ)
    (hnonBoolean : ∃ i, ¬ HasExactlyTwo (A i)) :
    IsBox Q f ∨ HasUnitWitness Q := by
  classical
  by_cases hbox : IsBox Q f
  · exact Or.inl hbox
  by_cases hunit : HasUnitWitness Q
  · exact Or.inr hunit
  rcases exists_mixedClosure_base
      hA hunary hPQ hproper hfull hperm hsync hf
      hσbox hτmem hbox hunit with
    ⟨y, hyP, hclosure⟩
  rcases hproper with ⟨ω, hωQ⟩
  exact False.elim
    (false_of_mixedClosure_nonBoolean
      hA hunary hPQ hperm hyP hclosure hnonBoolean hωQ)

/-- A choice of the complement operation on a two-element type. -/
structure Complementation (α : Type uA) where
  complement : α → α
  complement_ne : ∀ a, complement a ≠ a
  eq_or_eq_complement : ∀ a x, x = a ∨ x = complement a

/-- Every two-element type admits a complementation. -/
lemma exists_complementation {α : Type uA}
    (hα : HasExactlyTwo α) : Nonempty (Complementation α) := by
  classical
  rcases hα with ⟨p, q, hpq, hall⟩
  let complement : α → α := fun a ↦ if a = p then q else p
  refine ⟨{
    complement := complement
    complement_ne := ?_
    eq_or_eq_complement := ?_
  }⟩
  · intro a
    by_cases ha : a = p
    · subst a
      simpa [complement] using hpq.symm
    · change (if a = p then q else p) ≠ a
      rw [if_neg ha]
      exact Ne.symm ha
  · intro a x
    by_cases ha : a = p
    · subst a
      simpa [complement] using hall x
    · have haq : a = q := by
        rcases hall a with hap | haq
        · exact False.elim (ha hap)
        · exact haq
      rcases hall x with hxp | hxq
      · exact Or.inr (by simpa [complement, ha] using hxp)
      · exact Or.inl (hxq.trans haq.symm)

/-- Any two distinct elements enumerate a two-element type. -/
lemma eq_or_eq_of_hasExactlyTwo
    {α : Type uA} (htwo : HasExactlyTwo α)
    {a b : α} (hab : a ≠ b) (x : α) :
    x = a ∨ x = b := by
  rcases htwo with ⟨p, q, hpq, hall⟩
  rcases hall a with ha | ha
  · rcases hall b with hb | hb
    · exact False.elim (hab (ha.trans hb.symm))
    · rcases hall x with hx | hx
      · exact Or.inl (hx.trans ha.symm)
      · exact Or.inr (hx.trans hb.symm)
  · rcases hall b with hb | hb
    · rcases hall x with hx | hx
      · exact Or.inr (hx.trans hb.symm)
      · exact Or.inl (hx.trans ha.symm)
    · exact False.elim (hab (ha.trans hb.symm))

/-- An injective self-map of a two-element type is surjective. -/
lemma surjective_of_injective_exactlyTwo
    {α : Type uA} (htwo : HasExactlyTwo α)
    {u : α → α} (hinj : Function.Injective u) :
    Function.Surjective u := by
  rcases htwo with ⟨a, b, hab, hall⟩
  have huab : u a ≠ u b := fun h ↦ hab (hinj h)
  have hua := eq_or_eq_of_hasExactlyTwo
    ⟨a, b, hab, hall⟩ (a := a) (b := b) hab (u a)
  have hub := eq_or_eq_of_hasExactlyTwo
    ⟨a, b, hab, hall⟩ (a := a) (b := b) hab (u b)
  intro y
  rcases hall y with hy | hy
  · rcases hua with hua | hua
    · exact ⟨a, hua.trans hy.symm⟩
    · rcases hub with hub | hub
      · exact ⟨b, hub.trans hy.symm⟩
      · exact False.elim (huab (hua.trans hub.symm))
  · rcases hua with hua | hua
    · rcases hub with hub | hub
      · exact False.elim (huab (hua.trans hub.symm))
      · exact ⟨b, hub.trans hy.symm⟩
    · exact ⟨a, hua.trans hy.symm⟩

/-- A non-bijective self-map of a two-element type is constant. -/
lemma constant_of_not_bijective_exactlyTwo
    {α : Type uA} (htwo : HasExactlyTwo α)
    {u : α → α} (hnot : ¬ Function.Bijective u) :
    ∃ c, ∀ x, u x = c := by
  classical
  have hninj : ¬ Function.Injective u := by
    intro hinj
    exact hnot ⟨hinj, surjective_of_injective_exactlyTwo htwo hinj⟩
  obtain ⟨a, b, huab, hab⟩ :
      ∃ a b, u a = u b ∧ a ≠ b := by
    by_contra hnone
    apply hninj
    intro a b hu
    by_contra hab
    exact hnone ⟨a, b, hu, hab⟩
  refine ⟨u a, ?_⟩
  intro x
  rcases eq_or_eq_of_hasExactlyTwo htwo hab x with hx | hx
  · exact congrArg u hx
  · exact (congrArg u hx).trans huab.symm

/-- Every permutation of a two-element type is an involution. -/
lemma involutive_of_bijective_exactlyTwo
    {α : Type uA} (htwo : HasExactlyTwo α)
    {u : α → α} (hbij : Function.Bijective u) :
    Function.LeftInverse u u := by
  intro x
  by_cases hux : u x = x
  · exact congrArg u hux |>.trans hux
  · rcases eq_or_eq_of_hasExactlyTwo htwo (Ne.symm hux) (u (u x)) with h | h
    · exact h
    · exact False.elim (hux (hbij.1 h))

/-- Compose each first section of a binary operation with itself. -/
def squareFirstSections (f : Operation 2 A A) : Operation 2 A A :=
  fun i input ↦
    f i (binaryPair (input 0)
      (f i (binaryPair (input 0) (input 1))))

@[simp] lemma squareFirstSections_pair
    (f : Operation 2 A A) (i : ι) (a b : A i) :
    squareFirstSections f i (binaryPair a b) =
      f i (binaryPair a (f i (binaryPair a b))) := rfl

/--
On Boolean alphabets, squaring a first section preserves its image.
-/
lemma squareFirstSections_image_iff
    (htwo : ∀ i, HasExactlyTwo (A i))
    {f : Operation 2 A A} (i : ι) (a value : A i) :
    (∃ b, squareFirstSections f i (binaryPair a b) = value) ↔
      ∃ b, f i (binaryPair a b) = value := by
  let u : A i → A i := fun b ↦ f i (binaryPair a b)
  by_cases hbij : Function.Bijective u
  · have hinv := involutive_of_bijective_exactlyTwo (htwo i) hbij
    constructor
    · intro _h
      exact hbij.2 value
    · intro h
      rcases h with ⟨b, hb⟩
      exact ⟨u b, by
        change u (u (u b)) = value
        rw [hinv (u b)]
        exact hb⟩
  · rcases constant_of_not_bijective_exactlyTwo (htwo i) hbij with
      ⟨c, hc⟩
    constructor <;> intro h
    · rcases h with ⟨b, hb⟩
      exact ⟨b, by
        change u (u b) = value at hb
        rw [hc (u b)] at hb
        exact (hc b).trans hb⟩
    · rcases h with ⟨b, hb⟩
      exact ⟨b, by
        change u (u b) = value
        rw [hc (u b)]
        exact (hc b).symm.trans hb⟩

/-- Squaring a Boolean permutation section produces the identity section. -/
lemma squared_firstSection_eq_identity
    (htwo : ∀ i, HasExactlyTwo (A i))
    {f : Operation 2 A A} {x : Tuple A}
    (hperm : ∀ i, FirstSectionIsPermutation f i (x i)) :
    firstSection (squareFirstSections f) x = (fun _ a ↦ a) := by
  funext i a
  change f i (binaryPair (x i) (f i (binaryPair (x i) a))) = a
  exact involutive_of_bijective_exactlyTwo (htwo i) (hperm i) a

/-- Squaring first sections preserves binary polymorphisms on Boolean alphabets. -/
lemma squareFirstSections_preserves
    (htwo : ∀ i, HasExactlyTwo (A i))
    (hunary : BoxTrivialAtArity P Q Φ 1)
    (hPQ : P ⊆ Q)
    (hperm : IsPermutationFamily Φ)
    {f : Operation 2 A A} (hf : Preserves P Q f) :
    Preserves P Q (squareFirstSections f) := by
  intro rows hrows
  rcases firstSection_classification hunary hf (hrows 0) with hmem | hbox
  · have hallperm : ∀ i,
        FirstSectionIsPermutation f i (rows 0 i) := by
      intro i
      exact hperm (firstSection f (rows 0)) hmem i
    have hout : applyOperation (squareFirstSections f) rows = rows 1 := by
      funext i
      change squareFirstSections f i (fun r ↦ rows r i) = rows 1 i
      rw [← binaryPair_eta (fun r ↦ rows r i)]
      change f i (binaryPair (rows 0 i)
        (f i (binaryPair (rows 0 i) (rows 1 i)))) = rows 1 i
      exact involutive_of_bijective_exactlyTwo
        (htwo i) (hallperm i) (rows 1 i)
    rw [hout]
    exact hPQ (hrows 1)
  · apply hbox
    intro i
    exact ⟨f i (binaryPair (rows 0 i) (rows 1 i)), rfl⟩

/-- Squaring Boolean first sections preserves the full coordinate image box. -/
lemma squareFirstSections_inImageBox_iff
    (htwo : ∀ i, HasExactlyTwo (A i))
    {f : Operation 2 A A} {y : Tuple A} :
    InImageBox (squareFirstSections f) y ↔ InImageBox f y := by
  constructor
  · intro hy i
    rcases hy i with ⟨input, hinput⟩
    rw [← binaryPair_eta input] at hinput
    rcases (squareFirstSections_image_iff htwo
      i (input 0) (y i)).1 ⟨input 1, hinput⟩ with ⟨b, hb⟩
    exact ⟨binaryPair (input 0) b, hb⟩
  · intro hy i
    rcases hy i with ⟨input, hinput⟩
    rw [← binaryPair_eta input] at hinput
    rcases (squareFirstSections_image_iff htwo
      i (input 0) (y i)).2 ⟨input 1, hinput⟩ with ⟨b, hb⟩
    exact ⟨binaryPair (input 0) b, hb⟩

/-- Squaring Boolean first sections preserves box type. -/
lemma squareFirstSections_isBox_iff
    (htwo : ∀ i, HasExactlyTwo (A i))
    {f : Operation 2 A A} :
    IsBox Q (squareFirstSections f) ↔ IsBox Q f := by
  constructor
  · intro hbox y hy
    exact hbox ((squareFirstSections_inImageBox_iff htwo).2 hy)
  · intro hbox y hy
    exact hbox ((squareFirstSections_inImageBox_iff htwo).1 hy)

/--
In the Boolean mixed case, the squared-section operation is neither dictator
nor box whenever the original operation is not box type.
-/
lemma squareFirstSections_not_boxTrivial
    [Nonempty ι]
    (htwo : ∀ i, HasExactlyTwo (A i))
    (hproper : ∃ z : Tuple A, z ∉ Q)
    (hperm : IsPermutationFamily Φ)
    {f : Operation 2 A A}
    {σ τ : Tuple A}
    (hσbox : UnaryIsBox Q (firstSection f σ))
    (hτmem : firstSection f τ ∈ Φ)
    (hfnotbox : ¬ IsBox Q f) :
    ¬ IsBoxTrivial Q Φ (squareFirstSections f) := by
  classical
  have hτperm : ∀ i, FirstSectionIsPermutation f i (τ i) := by
    intro i
    exact hperm (firstSection f τ) hτmem i
  have hτid :
      firstSection (squareFirstSections f) τ = (fun _ a ↦ a) :=
    squared_firstSection_eq_identity htwo hτperm
  rcases exists_not_surjective_of_unaryIsBox hproper hσbox with
    ⟨i, hinsigma⟩
  have hσnotbij : ¬ FirstSectionIsPermutation f i (σ i) :=
    fun h ↦ hinsigma h.2
  rcases constant_of_not_bijective_exactlyTwo
      (htwo i) hσnotbij with ⟨c, hc⟩
  rcases htwo i with ⟨p, q, hpq, hall⟩
  let d : A i := if c = p then q else p
  have hdc : d ≠ c := by
    by_cases hcp : c = p
    · subst c
      simpa [d] using hpq.symm
    · dsimp [d]
      rw [if_neg hcp]
      exact Ne.symm hcp
  have hσd :
      squareFirstSections f i (binaryPair (σ i) d) = c := by
    change f i (binaryPair (σ i)
      (f i (binaryPair (σ i) d))) = c
    exact hc _
  have hτd :
      squareFirstSections f i (binaryPair (τ i) d) = d := by
    change firstSection (squareFirstSections f) τ i d = d
    rw [hτid]
  intro htrivial
  rcases htrivial with hdict | hbox
  · rcases hdict with ⟨s, φ, hφmem, hφ⟩
    have hs : s = 0 ∨ s = 1 := by
      refine Fin.cases (Or.inl rfl) (fun r ↦ ?_) s
      have hr : r = 0 := Fin.eq_zero r
      subst r
      exact Or.inr rfl
    rcases hs with hs | hs
    · subst s
      let j : ι := Classical.choice inferInstance
      rcases htwo j with ⟨a, b, hab, hjall⟩
      let inputA : Fin 2 → A j := binaryPair (τ j) a
      let inputB : Fin 2 → A j := binaryPair (τ j) b
      have heq :
          squareFirstSections f j inputA =
            squareFirstSections f j inputB := by
        rw [hφ j inputA, hφ j inputB]
        rfl
      have houtA : squareFirstSections f j inputA = a := by
        change firstSection (squareFirstSections f) τ j a = a
        rw [hτid]
      have houtB : squareFirstSections f j inputB = b := by
        change firstSection (squareFirstSections f) τ j b = b
        rw [hτid]
      exact hab (houtA.symm.trans (heq.trans houtB))
    · subst s
      let inputτ : Fin 2 → A i := binaryPair (τ i) d
      let inputσ : Fin 2 → A i := binaryPair (σ i) d
      have heq :
          squareFirstSections f i inputτ =
            squareFirstSections f i inputσ := by
        rw [hφ i inputτ, hφ i inputσ]
        rfl
      have hcd : c = d := hσd.symm.trans (heq.symm.trans hτd)
      exact hdc hcd.symm
  · exact hfnotbox ((squareFirstSections_isBox_iff htwo).1 hbox)

/-- The squared Boolean operation therefore has a distinguished second section. -/
lemma exists_squared_secondSection_mem
    [Nonempty ι]
    (htwo : ∀ i, HasExactlyTwo (A i))
    (hunary : BoxTrivialAtArity P Q Φ 1)
    (hPQ : P ⊆ Q)
    (hproper : ∃ z : Tuple A, z ∉ Q)
    (hfull : HasFullProjections P)
    (hperm : IsPermutationFamily Φ)
    (hsync : IsSynchronous Φ)
    {f : Operation 2 A A} (hf : Preserves P Q f)
    {σ τ : Tuple A}
    (hσbox : UnaryIsBox Q (firstSection f σ))
    (hτmem : firstSection f τ ∈ Φ)
    (hfnotbox : ¬ IsBox Q f)
    (hnoUnit : ¬ HasUnitWitness Q) :
    ∃ y ∈ P, secondSection (squareFirstSections f) y ∈ Φ := by
  have hA : ∀ i, HasAtLeastTwo (A i) := by
    intro i
    rcases htwo i with ⟨a, b, hab, hall⟩
    exact ⟨a, b, hab⟩
  apply exists_secondSection_mem_of_not_boxTrivial
    hA hunary hPQ hproper hfull hperm hsync
    (squareFirstSections_preserves htwo hunary hPQ hperm hf)
    (squareFirstSections_not_boxTrivial
      htwo hproper hperm hσbox hτmem hfnotbox)
    hnoUnit

/-- The intermediate closure property in the Boolean mixed branch. -/
def HasBooleanMixedClosure
    (P Q : Relation A) (τ y : Tuple A) : Prop :=
  ∀ z ∈ P, z ≠ τ →
    ∀ w : Tuple A, (∀ i, z i ≠ τ i → w i ≠ y i) → w ∈ Q

/--
The distinguished second section of the squared operation yields the
Boolean-specific closure property.
-/
lemma squared_hasBooleanMixedClosure
    (htwo : ∀ i, HasExactlyTwo (A i))
    (hunary : BoxTrivialAtArity P Q Φ 1)
    (hperm : IsPermutationFamily Φ)
    {f : Operation 2 A A} (hf : Preserves P Q f)
    {τ y : Tuple A}
    (hτmem : firstSection f τ ∈ Φ)
    (hymem : secondSection (squareFirstSections f) y ∈ Φ) :
    HasBooleanMixedClosure P Q τ y := by
  classical
  have hτperm : ∀ i, FirstSectionIsPermutation f i (τ i) := by
    intro i
    exact hperm (firstSection f τ) hτmem i
  have hτid :
      firstSection (squareFirstSections f) τ = (fun _ a ↦ a) :=
    squared_firstSection_eq_identity htwo hτperm
  have hpermInput : ∀ i a,
      FirstSectionIsPermutation f i a → a = τ i := by
    intro i a ha
    apply (hperm
      (secondSection (squareFirstSections f) y) hymem i).1
    change squareFirstSections f i (binaryPair a (y i)) =
      squareFirstSections f i (binaryPair (τ i) (y i))
    have haid := involutive_of_bijective_exactlyTwo (htwo i) ha (y i)
    have hτiid :=
      involutive_of_bijective_exactlyTwo (htwo i) (hτperm i) (y i)
    exact haid.trans hτiid.symm
  intro z hzP hzτ
  rcases firstSection_classification hunary hf hzP with hmem | hbox
  · apply False.elim
    apply hzτ
    funext i
    exact hpermInput i (z i) (hperm (firstSection f z) hmem i)
  · intro w hw
    apply hbox
    intro i
    by_cases hzi : z i = τ i
    · change ∃ a, f i (binaryPair (z i) a) = w i
      rw [hzi]
      refine ⟨f i (binaryPair (τ i) (w i)), ?_⟩
      exact involutive_of_bijective_exactlyTwo
        (htwo i) (hτperm i) (w i)
    · have hnotbij : ¬ FirstSectionIsPermutation f i (z i) := by
        intro hbij
        exact hzi (hpermInput i (z i) hbij)
      rcases constant_of_not_bijective_exactlyTwo
          (htwo i) hnotbij with ⟨c, hc⟩
      have hcy : c ≠ y i := by
        intro hcy
        have heq :
            squareFirstSections f i (binaryPair (z i) (y i)) =
              squareFirstSections f i (binaryPair (τ i) (y i)) := by
          have hzout :
              squareFirstSections f i (binaryPair (z i) (y i)) = c := by
            change f i (binaryPair (z i)
              (f i (binaryPair (z i) (y i)))) = c
            exact hc _
          have hτout :
              squareFirstSections f i (binaryPair (τ i) (y i)) = y i := by
            change firstSection (squareFirstSections f) τ i (y i) = y i
            rw [hτid]
          exact hzout.trans (hcy.trans hτout.symm)
        exact hzi ((hperm
          (secondSection (squareFirstSections f) y) hymem i).1 heq)
      have hwy : w i = c := by
        rcases eq_or_eq_of_hasExactlyTwo
            (htwo i) hcy (w i) with hwc | hwy
        · exact hwc
        · exact False.elim (hw i hzi hwy)
      refine ⟨c, ?_⟩
      rw [hwy]
      exact hc c

/-- The final unary map in the Boolean mixed branch. -/
noncomputable def booleanMixedMap
    (τ ybar x : Tuple A) : UnaryMap A A := by
  classical
  exact fun i a ↦ if a = τ i then x i else ybar i

/-- Boolean mixed closure implies the generalized-upset obstruction. -/
lemma generalizedUpset_of_booleanMixedClosure
    (htwo : ∀ i, HasExactlyTwo (A i))
    (hunary : BoxTrivialAtArity P Q Φ 1)
    (hperm : IsPermutationFamily Φ)
    {τ y : Tuple A} (hyP : y ∈ P)
    (hclosure : HasBooleanMixedClosure P Q τ y) :
    HasGeneralizedUpset P Q := by
  classical
  let c : ∀ i, Complementation (A i) :=
    fun i ↦ Classical.choice (exists_complementation (htwo i))
  let ybar : Tuple A := fun i ↦ (c i).complement (y i)
  let τbar : Tuple A := fun i ↦ (c i).complement (τ i)
  have hybar : ∀ i, ybar i ≠ y i := by
    intro i
    exact (c i).complement_ne (y i)
  have hτbar : ∀ i, τbar i ≠ τ i := by
    intro i
    exact (c i).complement_ne (τ i)
  refine ⟨htwo, y, hyP, ?_⟩
  intro x hxQ hxy
  let η : UnaryMap A A := booleanMixedMap τ ybar x
  have hηpoly : IsUnaryPolymorphism P Q η := by
    intro z hzP
    by_cases hzτ : z = τ
    · subst z
      have hout : (fun i ↦ η i (τ i)) = x := by
        funext i
        simp [η, booleanMixedMap]
      rw [hout]
      exact hxQ
    · apply hclosure z hzP hzτ
      intro i hzi
      change booleanMixedMap τ ybar x i (z i) ≠ y i
      simp [booleanMixedMap, hzi, hybar i]
  have hi : ∃ i, x i ≠ y i := by
    by_contra hnone
    apply hxy
    funext i
    by_contra hne
    exact hnone ⟨i, hne⟩
  rcases hi with ⟨i₀, hxi₀⟩
  have hxi₀bar : x i₀ = ybar i₀ := by
    rcases (c i₀).eq_or_eq_complement (y i₀) (x i₀) with h | h
    · exact False.elim (hxi₀ h)
    · exact h
  have hηnotmem : η ∉ Φ := by
    intro hηmem
    have heq : η i₀ (τ i₀) = η i₀ (τbar i₀) := by
      simp [η, booleanMixedMap, hτbar i₀, hxi₀bar]
    have := (hperm η hηmem i₀).1 heq
    exact hτbar i₀ this.symm
  have hηbox : UnaryIsBox Q η := by
    rcases unary_classification hunary hηpoly with hmem | hbox
    · exact False.elim (hηnotmem hmem)
    · exact hbox
  intro z hz
  apply hηbox
  intro i
  rcases hz i with hzx | hzney
  · exact ⟨τ i, by simp [η, booleanMixedMap, hzx]⟩
  · have hzbar : z i = ybar i := by
      rcases (c i).eq_or_eq_complement (y i) (z i) with h | h
      · exact False.elim (hzney h)
      · exact h
    exact ⟨τbar i, by
      simp [η, booleanMixedMap, hτbar i, hzbar]⟩

/-- The all-Boolean mixed-section lemma from the proof of Theorem 1.4. -/
lemma mixedSections_boolean
    [Nonempty ι]
    (htwo : ∀ i, HasExactlyTwo (A i))
    (hunary : BoxTrivialAtArity P Q Φ 1)
    (hPQ : P ⊆ Q)
    (hproper : ∃ z : Tuple A, z ∉ Q)
    (hfull : HasFullProjections P)
    (hperm : IsPermutationFamily Φ)
    (hsync : IsSynchronous Φ)
    {f : Operation 2 A A} (hf : Preserves P Q f)
    {σ τ : Tuple A}
    (hσbox : UnaryIsBox Q (firstSection f σ))
    (hτmem : firstSection f τ ∈ Φ) :
    IsBoxTrivial Q Φ f ∨ HasUnitWitness Q ∨
      HasGeneralizedUpset P Q := by
  classical
  by_cases htrivial : IsBoxTrivial Q Φ f
  · exact Or.inl htrivial
  have hfnotbox : ¬ IsBox Q f := fun hbox ↦ htrivial (Or.inr hbox)
  by_cases hunit : HasUnitWitness Q
  · exact Or.inr (Or.inl hunit)
  rcases exists_squared_secondSection_mem
      htwo hunary hPQ hproper hfull hperm hsync hf
      hσbox hτmem hfnotbox hunit with
    ⟨y, hyP, hymem⟩
  have hclosure : HasBooleanMixedClosure P Q τ y :=
    squared_hasBooleanMixedClosure
      htwo hunary hperm hf hτmem hymem
  exact Or.inr (Or.inr
    (generalizedUpset_of_booleanMixedClosure
      htwo hunary hperm hyP hclosure))

/--
The Boolean branch of the all-dictator-sections argument. A relation with
full projections whose members are separated in every coordinate has exactly
two members; unary box-triviality then gives the generalized-upset closure.
-/
lemma generalizedUpset_of_boolean_separated
    [Nonempty ι]
    (htwo : ∀ i, HasExactlyTwo (A i))
    (hPQ : P ⊆ Q)
    (hfull : HasFullProjections P)
    (hseparate : ∀ {z w : Tuple A}, z ∈ P → w ∈ P →
      ∀ i, z i = w i → z = w)
    (hunary : BoxTrivialAtArity P Q Φ 1)
    (hperm : IsPermutationFamily Φ) :
    HasGeneralizedUpset P Q := by
  classical
  let c : ∀ i, Complementation (A i) :=
    fun i ↦ Classical.choice (exists_complementation (htwo i))
  let k : ι := Classical.choice inferInstance
  let a : A k := Classical.choose (htwo k)
  let y : Tuple A := completion hfull hseparate k a
  let b : A k := (c k).complement (y k)
  let ybar : Tuple A := completion hfull hseparate k b
  have hyP : y ∈ P := completion_mem hfull hseparate k a
  have hybarP : ybar ∈ P := completion_mem hfull hseparate k b
  have hybar_ne_y : ybar ≠ y := by
    intro heq
    have hk := congrFun heq k
    have hybark : ybar k = b :=
      completion_at hfull hseparate k b
    exact (c k).complement_ne (y k) (hybark.symm.trans hk)
  have hdiff : ∀ i, ybar i ≠ y i := by
    intro i hi
    exact hybar_ne_y (hseparate hybarP hyP i hi)
  have hbar : ∀ i, ybar i = (c i).complement (y i) := by
    intro i
    rcases (c i).eq_or_eq_complement (y i) (ybar i) with hi | hi
    · exact False.elim (hdiff i hi)
    · exact hi
  have hchoices : ∀ i t, t = y i ∨ t = ybar i := by
    intro i t
    rcases (c i).eq_or_eq_complement (y i) t with hi | hi
    · exact Or.inl hi
    · exact Or.inr (hi.trans (hbar i).symm)
  have hPtwo : ∀ x ∈ P, x = y ∨ x = ybar := by
    intro x hx
    rcases hchoices k (x k) with hxk | hxk
    · exact Or.inl (hseparate hx hyP k hxk)
    · exact Or.inr (hseparate hx hybarP k hxk)
  refine ⟨htwo, y, hyP, ?_⟩
  intro x hxQ hxy
  have hi : ∃ i, x i ≠ y i := by
    by_contra hnone
    apply hxy
    funext i
    by_contra hne
    exact hnone ⟨i, hne⟩
  rcases hi with ⟨i₀, hxi₀⟩
  have hxi₀bar : x i₀ = ybar i₀ := by
    rcases hchoices i₀ (x i₀) with hi | hi
    · exact False.elim (hxi₀ hi)
    · exact hi
  let η : UnaryMap A A := fun i t ↦
    if t = y i then ybar i else x i
  have hηpoly : IsUnaryPolymorphism P Q η := by
    intro z hz
    rcases hPtwo z hz with hzy | hzybar
    · subst z
      have hout : (fun i ↦ η i (y i)) = ybar := by
        funext i
        simp [η]
      rw [hout]
      exact hPQ hybarP
    · subst z
      have hout : (fun i ↦ η i (ybar i)) = x := by
        funext i
        simp [η, hdiff i]
      rw [hout]
      exact hxQ
  have hηnotmem : η ∉ Φ := by
    intro hηmem
    have heq :
        η i₀ (y i₀) = η i₀ (ybar i₀) := by
      simp [η, hdiff i₀, hxi₀bar]
    have := (hperm η hηmem i₀).1 heq
    exact hdiff i₀ this.symm
  have hηbox : UnaryIsBox Q η := by
    rcases unary_classification hunary hηpoly with hmem | hbox
    · exact False.elim (hηnotmem hmem)
    · exact hbox
  intro z hz
  apply hηbox
  intro i
  rcases hz i with hzx | hzney
  · refine ⟨ybar i, ?_⟩
    simpa [η, hdiff i] using hzx.symm
  · have hzbar : z i = ybar i := by
      rcases hchoices i (z i) with hzy | hzybar
      · exact False.elim (hzney hzy)
      · exact hzybar
    refine ⟨y i, ?_⟩
    simpa [η] using hzbar.symm

/--
The all-dictator-sections lemma from the proof of Theorem 1.4.

When every first and second section belongs to `Φ`, synchrony separates the
members of `P`; the preceding lemmas then force Boolean alphabets and produce
a generalized-upset obstruction.
-/
lemma allDictatorSections
    [Nonempty ι]
    (hA : ∀ i, HasAtLeastTwo (A i))
    (hunary : BoxTrivialAtArity P Q Φ 1)
    (hPQ : P ⊆ Q)
    (hproper : ∃ z : Tuple A, z ∉ Q)
    (hfull : HasFullProjections P)
    (hperm : IsPermutationFamily Φ)
    (hsync : IsSynchronous Φ)
    {f : Operation 2 A A}
    (hfirst : ∀ x ∈ P, firstSection f x ∈ Φ)
    (hsecond : ∀ x ∈ P, secondSection f x ∈ Φ) :
    HasGeneralizedUpset P Q := by
  have hseparate :
      ∀ {z w : Tuple A}, z ∈ P → w ∈ P →
        ∀ i, z i = w i → z = w := by
    intro z w hz hw i hi
    exact eq_of_eq_coordinate_of_allSections_mem
      hperm hsync hfirst hsecond hz hw i hi
  have htwo : ∀ i, HasExactlyTwo (A i) :=
    all_alphabets_boolean_of_separated
      hA hPQ hproper hfull hseparate hunary hperm hsync
  exact generalizedUpset_of_boolean_separated
    htwo hPQ hfull hseparate hunary hperm

/-- The binary operation associated with a generalized-upset obstruction. -/
noncomputable def generalizedUpsetOperation
    (c : ∀ i, Complementation (A i)) (y : Tuple A) :
    Operation 2 A A := by
  classical
  exact fun i x ↦
    if x 0 = y i ∧ x 1 = y i then y i else (c i).complement (y i)

/-- The generalized-upset operation has full image in every coordinate. -/
lemma generalizedUpsetOperation_full_image
    (c : ∀ i, Complementation (A i)) (y : Tuple A) :
    ∀ i a, ∃ x, generalizedUpsetOperation c y i x = a := by
  classical
  intro i a
  rcases (c i).eq_or_eq_complement (y i) a with ha | ha
  · let x : Fin 2 → A i := fun _ ↦ y i
    refine ⟨x, ?_⟩
    simp [generalizedUpsetOperation, x, ha]
  · let x : Fin 2 → A i :=
      Fin.cases ((c i).complement (y i)) (fun _ ↦ y i)
    refine ⟨x, ?_⟩
    have hne : (c i).complement (y i) ≠ y i :=
      (c i).complement_ne (y i)
    simp [generalizedUpsetOperation, x, hne, ha]

/--
A generalized-upset obstruction yields a binary polymorphism which is neither
dictator nor box type.
-/
lemma not_boxTrivialAtTwo_of_generalizedUpset
    [Nonempty ι]
    (hPQ : P ⊆ Q)
    (hproper : ∃ z : Tuple A, z ∉ Q)
    (hupset : HasGeneralizedUpset P Q) :
    ¬ BoxTrivialAtArity P Q Φ 2 := by
  classical
  rcases hupset with ⟨htwo, y, hyP, hupset⟩
  let c : ∀ i, Complementation (A i) :=
    fun i ↦ Classical.choice (exists_complementation (htwo i))
  let f : Operation 2 A A := generalizedUpsetOperation c y
  have hfpoly : Preserves P Q f := by
    intro rows hrows
    by_cases hfirst : rows 0 = y
    · have heq : applyOperation f rows = rows 1 := by
        funext i
        have h0 : rows 0 i = y i := congrFun hfirst i
        rcases (c i).eq_or_eq_complement (y i) (rows 1 i) with h1 | h1
        · simp [applyOperation, f, generalizedUpsetOperation, h0, h1]
        · have hne : rows 1 i ≠ y i :=
            fun h ↦ (c i).complement_ne (y i) (h1.symm.trans h)
          change (if rows 0 i = y i ∧ rows 1 i = y i
            then y i else (c i).complement (y i)) = rows 1 i
          rw [if_neg (fun h ↦ hne h.2)]
          exact h1.symm
      rw [heq]
      exact hPQ (hrows 1)
    · apply hupset (rows 0) (hPQ (hrows 0)) hfirst
      intro i
      by_cases h0 : rows 0 i = y i
      · by_cases h1 : rows 1 i = y i
        · exact Or.inl (by
            simp [applyOperation, f, generalizedUpsetOperation, h0, h1])
        · exact Or.inr (by
            simp [applyOperation, f, generalizedUpsetOperation, h0, h1,
              (c i).complement_ne (y i)])
      · exact Or.inr (by
          simp [applyOperation, f, generalizedUpsetOperation, h0,
            (c i).complement_ne (y i)])
  intro htrivial
  rcases htrivial f hfpoly with hdict | hbox
  · rcases hdict with ⟨s, φ, hφΦ, hφ⟩
    let i : ι := Classical.choice inferInstance
    let a := y i
    let b := (c i).complement a
    have hba : b ≠ a := (c i).complement_ne a
    have hs : s = 0 ∨ s = 1 := by
      refine Fin.cases (Or.inl rfl) (fun q ↦ ?_) s
      have hq : q = 0 := Fin.eq_zero q
      subst q
      exact Or.inr rfl
    rcases hs with hs | hs
    · subst s
      let x : Fin 2 → A i := Fin.cases a (fun _ ↦ a)
      let x' : Fin 2 → A i := Fin.cases a (fun _ ↦ b)
      have heq : f i x = f i x' := by
        rw [hφ i x, hφ i x']
        change φ i a = φ i a
        rfl
      have hx : f i x = a := by
        change (if a = y i ∧ a = y i
          then y i else (c i).complement (y i)) = a
        simp [a]
      have hx' : f i x' = b := by
        change (if a = y i ∧ b = y i
          then y i else (c i).complement (y i)) = b
        simp [a, b, hba]
      exact hba (hx'.symm.trans (heq.symm.trans hx))
    · subst s
      let x : Fin 2 → A i := Fin.cases a (fun _ ↦ a)
      let x' : Fin 2 → A i := Fin.cases b (fun _ ↦ a)
      have heq : f i x = f i x' := by
        rw [hφ i x, hφ i x']
        change φ i a = φ i a
        rfl
      have hx : f i x = a := by
        change (if a = y i ∧ a = y i
          then y i else (c i).complement (y i)) = a
        simp [a]
      have hx' : f i x' = b := by
        change (if b = y i ∧ a = y i
          then y i else (c i).complement (y i)) = b
        simp [a, b, hba]
      exact hba (hx'.symm.trans (heq.symm.trans hx))
  · rcases hproper with ⟨z, hz⟩
    apply hz
    apply hbox
    intro i
    exact generalizedUpsetOperation_full_image c y i (z i)

/-- Replace one coordinate of the first projection by a specified binary operation. -/
noncomputable def replaceCoordinate (i : ι)
    (special : (Fin 2 → A i) → A i) : Operation 2 A A := by
  classical
  intro j x
  by_cases hji : j = i
  · subst j
    exact special x
  · exact x 0

@[simp] lemma replaceCoordinate_at (i : ι)
    (special : (Fin 2 → A i) → A i) (x : Fin 2 → A i) :
    replaceCoordinate i special i x = special x := by
  simp [replaceCoordinate]

@[simp] lemma replaceCoordinate_away (i j : ι) (hji : j ≠ i)
    (special : (Fin 2 → A i) → A i) (x : Fin 2 → A j) :
    replaceCoordinate i special j x = x 0 := by
  simp [replaceCoordinate, hji]

/-- The exceptional coordinate operation used by a unit witness. -/
noncomputable def unitSpecial {α : Type uA} (b c : α)
    (x : Fin 2 → α) : α := by
  classical
  exact if x 0 = c ∧ x 1 = c then c else b

/-- The binary operation associated with a unit-witness obstruction. -/
noncomputable def unitWitnessOperation (i : ι) (b c : A i) :
    Operation 2 A A :=
  replaceCoordinate i (unitSpecial b c)

@[simp] lemma unitWitnessOperation_at (i : ι) (b c : A i)
    (x : Fin 2 → A i) :
    unitWitnessOperation i b c i x = unitSpecial b c x := by
  simp [unitWitnessOperation]

@[simp] lemma unitWitnessOperation_away (i j : ι) (hji : j ≠ i)
    (b c : A i) (x : Fin 2 → A j) :
    unitWitnessOperation i b c j x = x 0 := by
  simp [unitWitnessOperation, hji]

/--
A unit-witness obstruction yields a binary polymorphism which is neither
dictator nor box type.
-/
lemma not_boxTrivialAtTwo_of_unitWitness
    (hPQ : P ⊆ Q)
    (hproper : ∃ z : Tuple A, z ∉ Q)
    (hunit : HasUnitWitness Q) :
    ¬ BoxTrivialAtArity P Q Φ 2 := by
  classical
  rcases hunit with ⟨i, b, htwo, hforce⟩
  let cstruct : Complementation (A i) :=
    Classical.choice (exists_complementation htwo)
  let c : A i := cstruct.complement b
  have hcb : c ≠ b := cstruct.complement_ne b
  let f : Operation 2 A A := unitWitnessOperation i b c
  have hfpoly : Preserves P Q f := by
    intro rows hrows
    by_cases hcc : rows 0 i = c ∧ rows 1 i = c
    · have heq : applyOperation f rows = rows 0 := by
        funext j
        by_cases hji : j = i
        · subst j
          change unitWitnessOperation i b c i
            (fun r ↦ rows r i) = rows 0 i
          rw [unitWitnessOperation_at]
          simp [unitSpecial, hcc]
        · change unitWitnessOperation i b c j
            (fun r ↦ rows r j) = rows 0 j
          rw [unitWitnessOperation_away i j hji]
      rw [heq]
      exact hPQ (hrows 0)
    · apply hforce (applyOperation f rows)
      change unitWitnessOperation i b c i
        (fun r ↦ rows r i) = b
      rw [unitWitnessOperation_at]
      simp [unitSpecial, hcc]
  intro htrivial
  rcases htrivial f hfpoly with hdict | hbox
  · rcases hdict with ⟨s, φ, hφΦ, hφ⟩
    have hs : s = 0 ∨ s = 1 := by
      refine Fin.cases (Or.inl rfl) (fun q ↦ ?_) s
      have hq : q = 0 := Fin.eq_zero q
      subst q
      exact Or.inr rfl
    rcases hs with hs | hs
    · subst s
      let x : Fin 2 → A i := Fin.cases c (fun _ ↦ c)
      let x' : Fin 2 → A i := Fin.cases c (fun _ ↦ b)
      have heq : f i x = f i x' := by
        rw [hφ i x, hφ i x']
        change φ i c = φ i c
        rfl
      have hx : f i x = c := by
        change unitWitnessOperation i b c i x = c
        rw [unitWitnessOperation_at]
        change (if c = c ∧ c = c then c else b) = c
        simp
      have hx' : f i x' = b := by
        change unitWitnessOperation i b c i x' = b
        rw [unitWitnessOperation_at]
        have hbc : b ≠ c := Ne.symm hcb
        change (if c = c ∧ b = c then c else b) = b
        simp [hbc]
      exact hcb (hx.symm.trans (heq.trans hx'))
    · subst s
      let x : Fin 2 → A i := Fin.cases c (fun _ ↦ c)
      let x' : Fin 2 → A i := Fin.cases b (fun _ ↦ c)
      have heq : f i x = f i x' := by
        rw [hφ i x, hφ i x']
        change φ i c = φ i c
        rfl
      have hx : f i x = c := by
        change unitWitnessOperation i b c i x = c
        rw [unitWitnessOperation_at]
        change (if c = c ∧ c = c then c else b) = c
        simp
      have hx' : f i x' = b := by
        change unitWitnessOperation i b c i x' = b
        rw [unitWitnessOperation_at]
        have hbc : b ≠ c := Ne.symm hcb
        change (if b = c ∧ c = c then c else b) = b
        simp [hbc]
      exact hcb (hx.symm.trans (heq.trans hx'))
  · rcases hproper with ⟨z, hz⟩
    apply hz
    apply hbox
    intro j
    by_cases hji : j = i
    · subst j
      rcases cstruct.eq_or_eq_complement b (z i) with hzb | hzc
      · let x : Fin 2 → A i := fun _ ↦ b
        refine ⟨x, ?_⟩
        change unitWitnessOperation i b c i x = z i
        rw [unitWitnessOperation_at]
        have hbc : b ≠ c := Ne.symm hcb
        simp [unitSpecial, x, hbc, hzb]
      · let x : Fin 2 → A i := fun _ ↦ c
        refine ⟨x, ?_⟩
        change unitWitnessOperation i b c i x = z i
        rw [unitWitnessOperation_at]
        simp [unitSpecial, x, c, hzc]
    · let x : Fin 2 → A j := fun _ ↦ z j
      refine ⟨x, ?_⟩
      change unitWitnessOperation i b c j x = z j
      rw [unitWitnessOperation_away i j hji]

/-- The easy direction of Theorem 1.4. -/
lemma unary_and_no_obstructions_of_allArities
    [Nonempty ι]
    (hPQ : P ⊆ Q)
    (hproper : ∃ z : Tuple A, z ∉ Q)
    (hall : BoxTrivialAtAllArities P Q Φ) :
    BoxTrivialAtArity P Q Φ 1 ∧
      ¬ HasUnitWitness Q ∧ ¬ HasGeneralizedUpset P Q := by
  refine ⟨hall 1 (Nat.le_refl 1), ?_, ?_⟩
  · intro hunit
    exact not_boxTrivialAtTwo_of_unitWitness hPQ hproper hunit
      (hall 2 (Nat.succ_le_succ (Nat.zero_le 1)))
  · intro hupset
    exact not_boxTrivialAtTwo_of_generalizedUpset hPQ hproper hupset
      (hall 2 (Nat.succ_le_succ (Nat.zero_le 1)))

end BoxTriviality
