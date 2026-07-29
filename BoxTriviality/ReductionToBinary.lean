import BoxTriviality.Defs
import Mathlib.Data.Fin.Basic

/-!
# Reduction to binary

This file formalizes Theorem 1.3 of *Triviality of promise polymorphisms*.
-/

namespace BoxTriviality

universe uι uA uB

variable {ι : Type uι}
variable {A : ι → Type uA} {B : ι → Type uB}
variable {P : Relation A} {Q : Relation B}
variable {Φ : Set (UnaryMap A B)}

/-- An operation of box type is automatically a polymorphism. -/
lemma preserves_of_isBox {n : Nat} {f : Operation n A B}
    (hf : IsBox Q f) : Preserves P Q f := by
  intro x _
  apply hf
  intro i
  exact ⟨fun r ↦ x r i, rfl⟩

/--
If a dictator operation is a polymorphism, then the unary map occurring in
its dictator presentation is itself a unary polymorphism.
-/
lemma unary_polymorphism_of_dictator {n : Nat} {f : Operation n A B}
    (hf : Preserves P Q f) (s : Fin n) (φ : UnaryMap A B)
    (hφ : ∀ i x, f i x = φ i (x s)) :
    IsUnaryPolymorphism P Q φ := by
  intro x hx
  have hout := hf (fun _ ↦ x) (fun _ ↦ hx)
  have heq :
      applyOperation f (fun _ ↦ x) = (fun i ↦ φ i (x i)) := by
    funext i
    exact hφ i _
  rwa [heq] at hout

/--
A unary compression of `h`, based at the input `seed`.

The compression has image contained in that of `h`, contains `h seed`,
agrees with every essentially-unary presentation of `h`, and can be constant
only when `h` is constant with the same value.
-/
structure Compression {α : Type uA} {β : Type uB} {n : Nat}
    (h : (Fin n → α) → β) (seed : Fin n → α) where
  toFun : α → β
  image_le : ∀ a, ∃ x, h x = toFun a
  hits_seed : ∃ a, toFun a = h seed
  eq_of_eq_eval :
    ∀ (s : Fin n) (ψ : α → β), (∀ x, h x = ψ (x s)) → toFun = ψ
  eq_const_of_toFun_eq_const :
    ∀ c, (∀ a, toFun a = c) → ∀ x, h x = c

/--
A binary compression used in the certificate version of the theorem.

It stays inside the image of `h`, transfers constant values back to `h`, and
cannot depend on only one input when `h` is nonconstant.
-/
structure BinaryCompression {α : Type uA} {β : Type uB} {n : Nat}
    (h : (Fin n → α) → β) where
  toFun : (Fin 2 → α) → β
  image_le : ∀ x, ∃ y, h y = toFun x
  eq_const_of_toFun_eq_const :
    ∀ c, (∀ x, toFun x = c) → ∀ y, h y = c
  not_eq_eval_of_nonconstant :
    (∃ u v, h u ≠ h v) →
      ∀ (s : Fin 2) (ψ : α → β), ¬ (∀ x, toFun x = ψ (x s))

/--
Every function on a positive power of a type with at least two elements has
a compression based at any prescribed input.
-/
lemma exists_compression {α : Type uA} {β : Type uB} {n : Nat}
    (hn : 0 < n) (hα : HasAtLeastTwo α)
    (h : (Fin n → α) → β) (seed : Fin n → α) :
    Nonempty (Compression h seed) := by
  classical
  by_cases heval : ∃ (s : Fin n) (ψ : α → β), ∀ x, h x = ψ (x s)
  · rcases heval with ⟨s, ψ, hψ⟩
    refine ⟨{
      toFun := ψ
      image_le := ?_
      hits_seed := ?_
      eq_of_eq_eval := ?_
      eq_const_of_toFun_eq_const := ?_
    }⟩
    · intro a
      refine ⟨fun _ ↦ a, ?_⟩
      simpa using hψ (fun _ ↦ a)
    · exact ⟨seed s, (hψ seed).symm⟩
    · intro t χ hχ
      funext a
      have h₁ := hψ (fun _ ↦ a)
      have h₂ := hχ (fun _ ↦ a)
      exact h₁.symm.trans h₂
    · intro c hc x
      exact (hψ x).trans (hc (x s))
  · have hnonconst : ∃ x, h x ≠ h seed := by
      by_contra hno
      apply heval
      let s : Fin n := ⟨0, hn⟩
      refine ⟨s, fun _ ↦ h seed, ?_⟩
      intro x
      by_contra hx
      exact hno ⟨x, hx⟩
    rcases hnonconst with ⟨other, hother⟩
    rcases hα with ⟨a₀, a₁, ha⟩
    let g : α → β := fun a ↦ if a = a₀ then h seed else h other
    refine ⟨{
      toFun := g
      image_le := ?_
      hits_seed := ?_
      eq_of_eq_eval := ?_
      eq_const_of_toFun_eq_const := ?_
    }⟩
    · intro a
      by_cases h_eq : a = a₀
      · exact ⟨seed, by simp [g, h_eq]⟩
      · exact ⟨other, by simp [g, h_eq]⟩
    · exact ⟨a₀, by simp [g]⟩
    · intro s ψ hψ
      exact False.elim (heval ⟨s, ψ, hψ⟩)
    · intro c hc
      have h₀ : h seed = c := by simpa [g] using hc a₀
      have h₁ : h other = c := by
        have hne : a₁ ≠ a₀ := fun h ↦ ha h.symm
        simpa [g, hne] using hc a₁
      exact False.elim (hother (h₁.trans h₀.symm))

/-- Construct the binary compression used for certificate-triviality. -/
lemma exists_binaryCompression {α : Type uA} {β : Type uB} {n : Nat}
    (hα : HasAtLeastTwo α) (h : (Fin n → α) → β) :
    Nonempty (BinaryCompression h) := by
  classical
  rcases hα with ⟨a₀, a₁, ha⟩
  by_cases hnonconstant : ∃ u v, h u ≠ h v
  · rcases hnonconstant with ⟨u, v, huv⟩
    let g : (Fin 2 → α) → β :=
      fun x ↦ if x 0 = x 1 then h u else h v
    refine ⟨{
      toFun := g
      image_le := ?_
      eq_const_of_toFun_eq_const := ?_
      not_eq_eval_of_nonconstant := ?_
    }⟩
    · intro x
      by_cases hx : x 0 = x 1
      · exact ⟨u, by simp [g, hx]⟩
      · exact ⟨v, by simp [g, hx]⟩
    · intro c hc
      let diagonal : Fin 2 → α := fun _ ↦ a₀
      let offDiagonal : Fin 2 → α := Fin.cases a₀ (fun _ ↦ a₁)
      have hdiag : g diagonal = h u := by simp [g, diagonal]
      have hoff : g offDiagonal = h v := by
        have hne : offDiagonal 0 ≠ offDiagonal 1 := by
          change a₀ ≠ a₁
          exact ha
        simp [g, hne]
      exact False.elim (huv
        (hdiag.symm.trans ((hc diagonal).trans
          ((hc offDiagonal).symm.trans hoff))))
    · intro _ s ψ heval
      have hs : s = 0 ∨ s = 1 := by
        refine Fin.cases (Or.inl rfl) (fun q ↦ ?_) s
        have hq : q = 0 := Fin.eq_zero q
        subst q
        exact Or.inr rfl
      rcases hs with hs | hs
      · subst s
        let diagonal : Fin 2 → α := fun _ ↦ a₀
        let offDiagonal : Fin 2 → α := Fin.cases a₀ (fun _ ↦ a₁)
        have heq : g diagonal = g offDiagonal := by
          rw [heval diagonal, heval offDiagonal]
          change ψ a₀ = ψ a₀
          rfl
        have hdiag : g diagonal = h u := by simp [g, diagonal]
        have hoff : g offDiagonal = h v := by
          have hne : offDiagonal 0 ≠ offDiagonal 1 := by
            change a₀ ≠ a₁
            exact ha
          simp [g, hne]
        exact huv (hdiag.symm.trans (heq.trans hoff))
      · subst s
        let diagonal : Fin 2 → α := fun _ ↦ a₀
        let offDiagonal : Fin 2 → α := Fin.cases a₁ (fun _ ↦ a₀)
        have heq : g diagonal = g offDiagonal := by
          rw [heval diagonal, heval offDiagonal]
          change ψ a₀ = ψ a₀
          rfl
        have hdiag : g diagonal = h u := by simp [g, diagonal]
        have hoff : g offDiagonal = h v := by
          have hne : offDiagonal 0 ≠ offDiagonal 1 := by
            change a₁ ≠ a₀
            exact fun h ↦ ha h.symm
          simp [g, hne]
        exact huv (hdiag.symm.trans (heq.trans hoff))
  · let seed : Fin n → α := fun _ ↦ a₀
    have hconstant : ∀ x, h x = h seed := by
      intro x
      by_contra hx
      exact hnonconstant ⟨x, seed, hx⟩
    refine ⟨{
      toFun := fun _ ↦ h seed
      image_le := fun _ ↦ ⟨seed, rfl⟩
      eq_const_of_toFun_eq_const := ?_
      not_eq_eval_of_nonconstant := ?_
    }⟩
    · intro c hc x
      exact (hconstant x).trans (hc (fun _ ↦ a₀))
    · intro hfalse
      exact False.elim (hnonconstant hfalse)

/-- Fix the first row of an `(n+1)`-ary operation. -/
def fixFirst {n : Nat} (f : Operation (n + 1) A B) (a : Tuple A) :
    Operation n A B :=
  fun i x ↦ f i (Fin.cases (a i) x)

/-- Fixing a row belonging to `P` preserves the polymorphism property. -/
lemma preserves_fixFirst {n : Nat} {f : Operation (n + 1) A B}
    (hf : Preserves P Q f) {a : Tuple A} (ha : a ∈ P) :
    Preserves P Q (fixFirst f a) := by
  intro x hx
  have hout := hf (Fin.cases a x) (by
    intro r
    refine Fin.cases ha ?_ r
    intro s
    exact hx s)
  have heq :
      applyOperation f (Fin.cases a x) =
        applyOperation (fixFirst f a) x := by
    funext i
    apply congrArg (f i)
    funext r
    refine Fin.cases ?_ (fun _ ↦ ?_) r <;> rfl
  rwa [heq] at hout

/-- A coordinate section obtained by fixing the first argument. -/
def coordinateSection {n : Nat} (f : Operation (n + 1) A B)
    (i : ι) (a : A i) : (Fin n → A i) → B i :=
  fun x ↦ f i (Fin.cases a x)

/-- The tuple operation `fixFirst` is assembled from the coordinate sections. -/
lemma fixFirst_apply {n : Nat} (f : Operation (n + 1) A B)
    (a : Tuple A) (i : ι) :
    fixFirst f a i = coordinateSection f i (a i) :=
  rfl

/-- A nonconstant unary function cannot read two distinct independent coordinates. -/
lemma eval_coordinate_unique {α : Type uA} {β : Type uB} {n : Nat}
    {ψ : α → β} (hψ : ∃ a b, ψ a ≠ ψ b)
    {s t : Fin n} (h : ∀ x : Fin n → α, ψ (x s) = ψ (x t)) :
    s = t := by
  classical
  by_contra hst
  rcases hψ with ⟨a, b, hab⟩
  let x : Fin n → α := fun r ↦ if r = s then a else b
  have hx := h x
  have hts : t ≠ s := fun hts ↦ hst hts.symm
  apply hab
  simpa [x, hst, hts] using hx

/--
Induction step in the reduction to binary: box-triviality in arities `2` and
`n` implies box-triviality in arity `n+1`.
-/
theorem boxTrivial_succ {n : Nat}
    (hpos : 0 < n)
    (hA : ∀ i, HasAtLeastTwo (A i))
    (hP : HasFullProjections P)
    (hbinary : BoxTrivialAtArity P Q Φ 2)
    (hn : BoxTrivialAtArity P Q Φ n) :
    BoxTrivialAtArity P Q Φ (n + 1) := by
  classical
  intro f hf
  by_cases hfbox : IsBox Q f
  · exact Or.inr hfbox
  have hwitness :
      ∃ ω : Tuple B, InImageBox f ω ∧ ω ∉ Q := by
    by_contra h
    apply hfbox
    intro y hy
    by_contra hyQ
    exact h ⟨y, hy, hyQ⟩
  rcases hwitness with ⟨ω, hωimage, hωQ⟩

  let witnessInput : ∀ i, Fin (n + 1) → A i :=
    fun i ↦ Classical.choose (hωimage i)
  have hwitnessInput : ∀ i, f i (witnessInput i) = ω i :=
    fun i ↦ Classical.choose_spec (hωimage i)

  let α : Tuple A := fun i ↦ witnessInput i 0
  let tail : ∀ i, Fin n → A i := fun i r ↦ witnessInput i r.succ
  let base : ∀ i, A i := fun i ↦ Classical.choose (hA i)
  let seed : ∀ i, A i → Fin n → A i :=
    fun i a ↦ if a = α i then tail i else fun _ ↦ base i
  let secFun : ∀ i, A i → (Fin n → A i) → B i :=
    fun i a ↦ coordinateSection f i a
  let compression : ∀ i a, Compression (secFun i a) (seed i a) :=
    fun i a ↦ Classical.choice
      (exists_compression hpos (hA i) (secFun i a) (seed i a))
  let g : Operation 2 A B :=
    fun i x ↦ (compression i (x 1)).toFun (x 0)

  have hsection_witness :
      ∀ i, secFun i (α i) (tail i) = ω i := by
    intro i
    rw [show secFun i (α i) (tail i) =
        f i (witnessInput i) by
      apply congrArg (f i)
      funext r
      refine Fin.cases ?_ (fun s ↦ ?_) r
      · rfl
      · rfl]
    exact hwitnessInput i

  have hseed_alpha : ∀ i, seed i (α i) = tail i := by
    intro i
    simp [seed]

  have hωg : InImageBox g ω := by
    intro i
    rcases (compression i (α i)).hits_seed with ⟨a, ha⟩
    let x : Fin 2 → A i := Fin.cases a (fun _ ↦ α i)
    refine ⟨x, ?_⟩
    change (compression i (x 1)).toFun (x 0) = ω i
    have hx0 : x 0 = a := rfl
    have hx1 : x 1 = α i := rfl
    rw [hx0, hx1, ha, hseed_alpha i, hsection_witness i]

  have hg : Preserves P Q g := by
    intro rows hrows
    let a : Tuple A := rows 1
    have haP : a ∈ P := hrows 1
    have hfixed : Preserves P Q (fixFirst f a) :=
      preserves_fixFirst hf haP
    rcases hn (fixFirst f a) hfixed with hdict | hbox
    · rcases hdict with ⟨s, φ, hφΦ, hφ⟩
      have hcomp : ∀ i, (compression i (a i)).toFun = φ i := by
        intro i
        apply (compression i (a i)).eq_of_eq_eval s (φ i)
        exact hφ i
      have hφpoly : IsUnaryPolymorphism P Q φ :=
        unary_polymorphism_of_dictator hfixed s φ hφ
      have hout := hφpoly (rows 0) (hrows 0)
      have heq :
          applyOperation g rows = (fun i ↦ φ i (rows 0 i)) := by
        funext i
        change (compression i (a i)).toFun (rows 0 i) =
          φ i (rows 0 i)
        rw [hcomp i]
      rwa [heq]
    · apply hbox
      intro i
      change ∃ x, fixFirst f a i x =
        (compression i (a i)).toFun (rows 0 i)
      exact (compression i (a i)).image_le (rows 0 i)

  have hgdict : IsDictator Φ g := by
    rcases hbinary g hg with hdict | hbox
    · exact hdict
    · exact False.elim (hωQ (hbox hωg))

  rcases hgdict with ⟨selected, φ, hφΦ, hgφ⟩
  have hselected : selected = 0 ∨ selected = 1 := by
    refine Fin.cases (Or.inl rfl) (fun t ↦ ?_) selected
    have ht : t = 0 := Fin.eq_zero t
    subst t
    exact Or.inr rfl
  rcases hselected with hselected | hselected
  · subst selected
    have hcompφ :
        ∀ i a, (compression i a).toFun = φ i := by
      intro i a
      funext z
      let input : Fin 2 → A i := Fin.cases z (fun _ ↦ a)
      have h := hgφ i input
      exact h

    have hφpoly : IsUnaryPolymorphism P Q φ :=
      unary_polymorphism_of_dictator hg 0 φ hgφ

    have hsection_rep :
        ∀ i a, ∃ s : Fin n, ∀ x, secFun i a x = φ i (x s) := by
      intro i a
      rcases hP i a with ⟨p, hpP, hpi⟩
      have hfixed : Preserves P Q (fixFirst f p) :=
        preserves_fixFirst hf hpP
      rcases hn (fixFirst f p) hfixed with hdict | hbox
      · rcases hdict with ⟨s, ψ, hψΦ, hψ⟩
        have hcompψ :
            (compression i (p i)).toFun = ψ i := by
          apply (compression i (p i)).eq_of_eq_eval s (ψ i)
          exact hψ i
        refine ⟨s, ?_⟩
        intro x
        have hψi := hψ i x
        rw [fixFirst_apply] at hψi
        rw [← hpi]
        change coordinateSection f i (p i) x = φ i (x s)
        have heq : ψ i = φ i := hcompψ.symm.trans (hcompφ i (p i))
        rw [hψi, heq]
      · exfalso
        apply hωQ
        apply hbox
        intro j
        rcases (compression j (α j)).hits_seed with ⟨z, hz⟩
        have hzω :
            (compression j (α j)).toFun z = ω j := by
          rw [hz, hseed_alpha j, hsection_witness j]
        have htransport :
            (compression j (p j)).toFun z =
              (compression j (α j)).toFun z := by
          rw [hcompφ j (p j), hcompφ j (α j)]
        rcases (compression j (p j)).image_le z with ⟨x, hx⟩
        refine ⟨x, ?_⟩
        rw [fixFirst_apply]
        change coordinateSection f j (p j) x =
          (compression j (p j)).toFun z at hx
        rw [hx, htransport, hzω]

    let chosenCoordinate : ∀ i, A i → Fin n :=
      fun i a ↦ Classical.choose (hsection_rep i a)
    have hchosenCoordinate :
        ∀ i a x,
          secFun i a x = φ i (x (chosenCoordinate i a)) :=
      fun i a ↦ Classical.choose_spec (hsection_rep i a)

    have htuple_rep :
        ∀ p ∈ P, ∃ s : Fin n, ∀ i x, secFun i (p i) x = φ i (x s) := by
      intro p hpP
      have hfixed : Preserves P Q (fixFirst f p) :=
        preserves_fixFirst hf hpP
      rcases hn (fixFirst f p) hfixed with hdict | hbox
      · rcases hdict with ⟨s, ψ, hψΦ, hψ⟩
        refine ⟨s, ?_⟩
        intro i x
        have hcompψ :
            (compression i (p i)).toFun = ψ i := by
          apply (compression i (p i)).eq_of_eq_eval s (ψ i)
          exact hψ i
        have heq : ψ i = φ i := hcompψ.symm.trans (hcompφ i (p i))
        have hi := hψ i x
        rw [fixFirst_apply] at hi
        rwa [heq] at hi
      · exfalso
        apply hωQ
        apply hbox
        intro j
        rcases (compression j (α j)).hits_seed with ⟨z, hz⟩
        have hzω :
            (compression j (α j)).toFun z = ω j := by
          rw [hz, hseed_alpha j, hsection_witness j]
        have htransport :
            (compression j (p j)).toFun z =
              (compression j (α j)).toFun z := by
          rw [hcompφ j (p j), hcompφ j (α j)]
        rcases (compression j (p j)).image_le z with ⟨x, hx⟩
        refine ⟨x, ?_⟩
        rw [fixFirst_apply]
        change coordinateSection f j (p j) x =
          (compression j (p j)).toFun z at hx
        rw [hx, htransport, hzω]

    let Varies : ι → Prop :=
      fun i ↦ ∃ a b : A i, φ i a ≠ φ i b

    have hconstant :
        ∀ i, ¬ Varies i → ∀ a b, φ i a = φ i b := by
      intro i hi a b
      by_contra hab
      exact hi ⟨a, b, hab⟩

    have hcooccur :
        ∀ p ∈ P, ∀ i j, Varies i → Varies j →
          chosenCoordinate i (p i) = chosenCoordinate j (p j) := by
      intro p hpP i j hi hj
      rcases htuple_rep p hpP with ⟨s, hs⟩
      have his : chosenCoordinate i (p i) = s := by
        apply eval_coordinate_unique hi
        intro x
        calc
          φ i (x (chosenCoordinate i (p i))) =
              secFun i (p i) x := (hchosenCoordinate i (p i) x).symm
          _ = φ i (x s) := hs i x
      have hjs : chosenCoordinate j (p j) = s := by
        apply eval_coordinate_unique hj
        intro x
        calc
          φ j (x (chosenCoordinate j (p j))) =
              secFun j (p j) x := (hchosenCoordinate j (p j) x).symm
          _ = φ j (x s) := hs j x
      exact his.trans hjs.symm

    have haligned :
        ∃ s : Fin n, ∀ i, Varies i →
          ∀ a, chosenCoordinate i a = s := by
      by_contra hnotAligned
      have hvaries : ∃ i, Varies i := by
        by_contra hnone
        apply hnotAligned
        refine ⟨⟨0, hpos⟩, ?_⟩
        intro i hi
        exact False.elim (hnone ⟨i, hi⟩)
      rcases hvaries with ⟨i₀, hi₀⟩
      let a₀ : A i₀ := Classical.choose (hA i₀)
      let s₀ : Fin n := chosenCoordinate i₀ a₀
      have hdiff :
          ∃ i, Varies i ∧ ∃ a, chosenCoordinate i a ≠ s₀ := by
        by_contra hnone
        apply hnotAligned
        refine ⟨s₀, ?_⟩
        intro i hi a
        by_contra hne
        exact hnone ⟨i, hi, a, hne⟩
      rcases hdiff with ⟨i₁, hi₁, a₁, ha₁⟩
      rcases hP i₀ a₀ with ⟨p₀, hp₀P, hp₀i⟩
      rcases hP i₁ a₁ with ⟨p₁, hp₁P, hp₁i⟩

      have hp₀label :
          ∀ i, Varies i → chosenCoordinate i (p₀ i) = s₀ := by
        intro i hi
        have h := hcooccur p₀ hp₀P i i₀ hi hi₀
        change chosenCoordinate i (p₀ i) =
          chosenCoordinate i₀ a₀
        exact h.trans (congrArg (chosenCoordinate i₀) hp₀i)

      have hp₁label :
          ∀ i, Varies i → chosenCoordinate i (p₁ i) ≠ s₀ := by
        intro i hi heq
        have h := hcooccur p₁ hp₁P i i₁ hi hi₁
        apply ha₁
        calc
          chosenCoordinate i₁ a₁ =
              chosenCoordinate i₁ (p₁ i₁) :=
            congrArg (chosenCoordinate i₁) hp₁i.symm
          _ = chosenCoordinate i (p₁ i) := h.symm
          _ = s₀ := heq

      let χ : Operation 2 A B :=
        fun i x ↦
          if chosenCoordinate i (x 0) = s₀
          then φ i (x 0)
          else φ i (x 1)

      have hχpoly : Preserves P Q χ := by
        intro rows hrows
        by_cases hcase :
            chosenCoordinate i₀ (rows 0 i₀) = s₀
        · have heq :
              applyOperation χ rows =
                (fun i ↦ φ i (rows 0 i)) := by
            funext i
            by_cases hi : Varies i
            · have hilabel :
                  chosenCoordinate i (rows 0 i) = s₀ := by
                exact (hcooccur (rows 0) (hrows 0) i i₀ hi hi₀).trans hcase
              simp [applyOperation, χ, hilabel]
            · by_cases hilabel :
                  chosenCoordinate i (rows 0 i) = s₀
              · simp [applyOperation, χ, hilabel]
              · simp [applyOperation, χ, hilabel,
                  hconstant i hi (rows 1 i) (rows 0 i)]
          rw [heq]
          exact hφpoly (rows 0) (hrows 0)
        · have heq :
              applyOperation χ rows =
                (fun i ↦ φ i (rows 1 i)) := by
            funext i
            by_cases hi : Varies i
            · have hilabel :
                  chosenCoordinate i (rows 0 i) ≠ s₀ := by
                intro hilabel
                apply hcase
                exact (hcooccur (rows 0) (hrows 0) i i₀ hi hi₀).symm.trans
                  hilabel
              simp [applyOperation, χ, hilabel]
            · by_cases hilabel :
                  chosenCoordinate i (rows 0 i) = s₀
              · simp [applyOperation, χ, hilabel,
                  hconstant i hi (rows 0 i) (rows 1 i)]
              · simp [applyOperation, χ, hilabel]
          rw [heq]
          exact hφpoly (rows 1) (hrows 1)

      have hωφ : ∀ i, ∃ a, φ i a = ω i := by
        intro i
        rcases (compression i (α i)).hits_seed with ⟨a, ha⟩
        refine ⟨a, ?_⟩
        rw [← congrFun (hcompφ i (α i)) a]
        rw [ha, hseed_alpha i, hsection_witness i]

      have hωχ : InImageBox χ ω := by
        intro i
        rcases hωφ i with ⟨a, ha⟩
        let input : Fin 2 → A i := fun _ ↦ a
        refine ⟨input, ?_⟩
        change (if chosenCoordinate i a = s₀
          then φ i a else φ i a) = ω i
        simp [ha]

      have hχnotBox : ¬ IsBox Q χ :=
        fun hbox ↦ hωQ (hbox hωχ)

      have hχnotDictator : ¬ IsDictator Φ χ := by
        intro hdict
        have hi₀copy := hi₀
        rcases hi₀copy with ⟨u, v, huv⟩
        have ht : ∃ t, φ i₀ t ≠ φ i₀ (p₀ i₀) := by
          by_cases hu : φ i₀ u ≠ φ i₀ (p₀ i₀)
          · exact ⟨u, hu⟩
          · refine ⟨v, ?_⟩
            intro hv
            apply huv
            exact (not_ne_iff.mp hu).trans hv.symm
        rcases ht with ⟨t, ht⟩
        rcases hdict with ⟨r, ψ, hψΦ, hψ⟩
        have hr : r = 0 ∨ r = 1 := by
          refine Fin.cases (Or.inl rfl) (fun q ↦ ?_) r
          have hq : q = 0 := Fin.eq_zero q
          subst q
          exact Or.inr rfl
        rcases hr with hr | hr
        · subst r
          let xu : Fin 2 → A i₀ := Fin.cases (p₁ i₀) (fun _ ↦ u)
          let xv : Fin 2 → A i₀ := Fin.cases (p₁ i₀) (fun _ ↦ v)
          have hsame : χ i₀ xu = χ i₀ xv := by
            rw [hψ i₀ xu, hψ i₀ xv]
            simp [xu, xv]
          have hxu : χ i₀ xu = φ i₀ u := by
            change (if chosenCoordinate i₀ (p₁ i₀) = s₀
              then φ i₀ (p₁ i₀) else φ i₀ u) = φ i₀ u
            simp [hp₁label i₀ hi₀]
          have hxv : χ i₀ xv = φ i₀ v := by
            change (if chosenCoordinate i₀ (p₁ i₀) = s₀
              then φ i₀ (p₁ i₀) else φ i₀ v) = φ i₀ v
            simp [hp₁label i₀ hi₀]
          exact huv (hxu.symm.trans (hsame.trans hxv))
        · subst r
          let xc : Fin 2 → A i₀ := Fin.cases (p₀ i₀) (fun _ ↦ t)
          let xd : Fin 2 → A i₀ := Fin.cases (p₁ i₀) (fun _ ↦ t)
          have hsame : χ i₀ xc = χ i₀ xd := by
            rw [hψ i₀ xc, hψ i₀ xd]
            change ψ i₀ t = ψ i₀ t
            rfl
          have hxc : χ i₀ xc = φ i₀ (p₀ i₀) := by
            change (if chosenCoordinate i₀ (p₀ i₀) = s₀
              then φ i₀ (p₀ i₀) else φ i₀ t) =
                φ i₀ (p₀ i₀)
            simp [hp₀label i₀ hi₀]
          have hxd : χ i₀ xd = φ i₀ t := by
            change (if chosenCoordinate i₀ (p₁ i₀) = s₀
              then φ i₀ (p₁ i₀) else φ i₀ t) = φ i₀ t
            simp [hp₁label i₀ hi₀]
          exact ht (hxd.symm.trans (hsame.symm.trans hxc))

      rcases hbinary χ hχpoly with hdict | hbox
      · exact hχnotDictator hdict
      · exact hχnotBox hbox

    rcases haligned with ⟨s, hs⟩
    exact Or.inl ⟨s.succ, φ, hφΦ, by
      intro i x
      let a : A i := x 0
      let xs : Fin n → A i := fun r ↦ x r.succ
      have hx : Fin.cases a xs = x := by
        funext r
        refine Fin.cases ?_ (fun _ ↦ ?_) r <;> rfl
      calc
        f i x = secFun i a xs := by
          change f i x = f i (Fin.cases a xs)
          rw [hx]
        _ = φ i (xs (chosenCoordinate i a)) :=
          hchosenCoordinate i a xs
        _ = φ i (xs s) := by
          by_cases hi : Varies i
          · rw [hs i hi a]
          · exact hconstant i hi _ _
        _ = φ i (x s.succ) := rfl⟩
  · subst selected
    have hcomp_const :
        ∀ i a z, (compression i a).toFun z = φ i a := by
      intro i a z
      let input : Fin 2 → A i := Fin.cases z (fun _ ↦ a)
      have h := hgφ i input
      exact h
    have hsection_const :
        ∀ i a x, secFun i a x = φ i a := by
      intro i a
      exact (compression i a).eq_const_of_toFun_eq_const
        (φ i a) (hcomp_const i a)
    exact Or.inl ⟨0, φ, hφΦ, by
      intro i x
      let a : A i := x 0
      let xs : Fin n → A i := fun r ↦ x r.succ
      have hx : Fin.cases a xs = x := by
        funext r
        refine Fin.cases ?_ (fun _ ↦ ?_) r <;> rfl
      calc
        f i x = secFun i a xs := by
          change f i x = f i (Fin.cases a xs)
          rw [hx]
        _ = φ i a := hsection_const i a xs
        _ = φ i (x 0) := rfl⟩

/-- Binary box-triviality implies unary box-triviality. -/
lemma boxTrivial_one_of_two
    (hbinary : BoxTrivialAtArity P Q Φ 2) :
    BoxTrivialAtArity P Q Φ 1 := by
  classical
  intro f hf
  let g : Operation 2 A B :=
    fun i x ↦ f i (fun _ ↦ x 0)
  have hg : Preserves P Q g := by
    intro rows hrows
    have hout := hf (fun _ ↦ rows 0) (fun _ ↦ hrows 0)
    have heq :
        applyOperation g rows =
          applyOperation f (fun _ ↦ rows 0) := by
      funext i
      rfl
    rwa [heq]
  rcases hbinary g hg with hdict | hbox
  · rcases hdict with ⟨s, φ, hφΦ, hφ⟩
    exact Or.inl ⟨0, φ, hφΦ, by
      intro i x
      let a := x 0
      let input : Fin 2 → A i := fun _ ↦ a
      have hi := hφ i input
      change f i (fun _ ↦ a) = φ i a at hi
      have hxeq : (fun _ : Fin 1 ↦ a) = x := by
        funext r
        rw [Fin.eq_zero r]
      rw [hxeq] at hi
      exact hi⟩
  · exact Or.inr (by
      intro y hy
      apply hbox
      intro i
      rcases hy i with ⟨x, hx⟩
      let input : Fin 2 → A i := fun _ ↦ x 0
      refine ⟨input, ?_⟩
      change f i (fun _ ↦ x 0) = y i
      have hxeq : (fun _ : Fin 1 ↦ x 0) = x := by
        funext r
        rw [Fin.eq_zero r]
      rwa [hxeq])

/--
Theorem 1.3: a relation pair is box-trivial in every positive arity if and
only if it is box-trivial in arity two.
-/
theorem boxTrivialAtAllArities_iff_binary
    (hA : ∀ i, HasAtLeastTwo (A i))
    (hP : HasFullProjections P) :
    BoxTrivialAtAllArities P Q Φ ↔ BoxTrivialAtArity P Q Φ 2 := by
  constructor
  · intro hall
    exact hall 2 (Nat.succ_le_succ (Nat.zero_le 1))
  · intro hbinary
    have hone : BoxTrivialAtArity P Q Φ 1 :=
      boxTrivial_one_of_two hbinary
    intro n hn
    induction n using Nat.strong_induction_on with
    | h n ih =>
        cases n with
        | zero => exact False.elim (Nat.not_succ_le_zero 0 hn)
        | succ n =>
            cases n with
            | zero => exact hone
            | succ k =>
                have hprevious :
                    BoxTrivialAtArity P Q Φ (Nat.succ k) :=
                  ih (Nat.succ k) (Nat.lt_succ_self _)
                    (Nat.succ_le_succ (Nat.zero_le k))
                simpa [Nat.succ_eq_add_one] using
                  boxTrivial_succ (n := Nat.succ k) (Nat.zero_lt_succ k)
                    hA hP hbinary hprevious

/-- Certificate type implies box type. -/
lemma isBox_of_isCertificate {n : Nat} {f : Operation n A B}
    (hcert : IsCertificate Q f) : IsBox Q f := by
  rcases hcert with ⟨I, δ, hconstant, hforce⟩
  intro y hy
  apply hforce y
  intro i hi
  rcases hy i with ⟨x, hx⟩
  exact hx.symm.trans (hconstant i hi x)

/--
Corollary 3.3: certificate-triviality in all positive arities is equivalent
to certificate-triviality in arity two.
-/
theorem certificateTrivialAtAllArities_iff_binary
    (hA : ∀ i, HasAtLeastTwo (A i))
    (hP : HasFullProjections P) :
    CertificateTrivialAtAllArities P Q Φ ↔
      CertificateTrivialAtArity P Q Φ 2 := by
  classical
  constructor
  · intro hall
    exact hall 2 (Nat.succ_le_succ (Nat.zero_le 1))
  · intro hcertificateBinary
    have hboxBinary : BoxTrivialAtArity P Q Φ 2 := by
      intro f hf
      rcases hcertificateBinary f hf with hdict | hcert
      · exact Or.inl hdict
      · exact Or.inr (isBox_of_isCertificate hcert)
    have hboxAll : BoxTrivialAtAllArities P Q Φ :=
      (boxTrivialAtAllArities_iff_binary hA hP).2 hboxBinary
    intro n hn f hf
    rcases hboxAll n hn f hf with hdict | hbox
    · exact Or.inl hdict
    · by_cases hallconstant :
          ∀ i, ∃ c, ∀ x : Fin n → A i, f i x = c
      · let value : ∀ i, B i :=
          fun i ↦ Classical.choose (hallconstant i)
        have hvalue :
            ∀ i x, f i x = value i :=
          fun i ↦ Classical.choose_spec (hallconstant i)
        let I : Set ι := fun _ ↦ True
        let δ : ∀ i, i ∈ I → B i := fun i _ ↦ value i
        exact Or.inr ⟨I, δ, by
          constructor
          · intro i hi x
            exact hvalue i x
          · intro y hy
            apply hbox
            intro i
            let a : A i := Classical.choose (hA i)
            let x : Fin n → A i := fun _ ↦ a
            refine ⟨x, ?_⟩
            calc
              f i x = value i := hvalue i x
              _ = δ i True.intro := rfl
              _ = y i := (hy i True.intro).symm⟩
      · have hsomeNonconstant :
            ∃ i, ¬ ∃ c, ∀ x : Fin n → A i, f i x = c := by
          by_contra hnone
          apply hallconstant
          intro i
          by_contra hi
          exact hnone ⟨i, hi⟩
        rcases hsomeNonconstant with ⟨i₀, hi₀⟩
        have hfi₀ :
            ∃ u v : Fin n → A i₀, f i₀ u ≠ f i₀ v := by
          by_contra hnone
          apply hi₀
          let a : A i₀ := Classical.choose (hA i₀)
          let seed : Fin n → A i₀ := fun _ ↦ a
          refine ⟨f i₀ seed, ?_⟩
          intro x
          by_contra hx
          exact hnone ⟨x, seed, hx⟩
        let compression : ∀ i, BinaryCompression (f i) :=
          fun i ↦ Classical.choice (exists_binaryCompression (hA i) (f i))
        let g : Operation 2 A B :=
          fun i ↦ (compression i).toFun
        have hgbox : IsBox Q g := by
          intro y hy
          apply hbox
          intro i
          rcases hy i with ⟨x, hx⟩
          rcases (compression i).image_le x with ⟨z, hz⟩
          exact ⟨z, hz.trans hx⟩
        have hgpoly : Preserves P Q g :=
          preserves_of_isBox hgbox
        rcases hcertificateBinary g hgpoly with hdict | hcert
        · rcases hdict with ⟨s, φ, hφΦ, hφ⟩
          exact False.elim
            ((compression i₀).not_eq_eval_of_nonconstant
              hfi₀ s (φ i₀) (hφ i₀))
        · rcases hcert with ⟨I, δ, hgconstant, hforce⟩
          exact Or.inr ⟨I, δ, by
            constructor
            · intro i hi
              exact (compression i).eq_const_of_toFun_eq_const
                (δ i hi) (hgconstant i hi)
            · exact hforce⟩

end BoxTriviality
