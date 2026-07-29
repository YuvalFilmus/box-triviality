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
