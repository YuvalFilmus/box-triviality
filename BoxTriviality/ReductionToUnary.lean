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
