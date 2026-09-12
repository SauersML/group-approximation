import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.PUnit
import GroupApproximation.Monsters.TwoConjugacyClasses

/-!
# Verbal completeness and what it forces

This module defines verbal completeness, proves that the definition is
inhabited, and derives its elementary consequences.

A group is verbally complete when every equation `v(x₁, …, x_m) = g` with `v` a
nontrivial element of a free group is solvable.  Three consequences follow by
choosing `v`:

* every nontrivial word map is surjective, which is the definition restated;
* the group is divisible -- take `v = X ^ n`;
* every element is a single commutator, i.e. the commutator width is one --
  take `v = ⁅X₁, X₂⁆`.

Combined with torsion-freeness and two conjugacy classes, the last of these is
what makes stable commutator length vanish: `cl (gⁿ) ≤ 1` for every `n`, so the
limit defining `scl` is zero.  Stable commutator length itself is not defined
in this library, so that statement appears here only in the form
`exists_commutatorElement_eq_pow`, which is the input any definition of it
would consume.

The two word choices need their words to be nontrivial in the free group, and
that is the only real work below: `X ^ n` is detected by the abelianization
`FreeGroup (Fin 1) → Multiplicative ℤ`, and `⁅X₁, X₂⁆` by evaluating in
`Equiv.Perm (Fin 3)`, where the commutator of two transpositions is a
three-cycle.
-/

namespace GroupApproximation.Monsters

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- A group is verbally complete when every equation given by a nontrivial
word has a solution. -/
def IsVerballyComplete (G : Type*) [Group G] : Prop :=
  ∀ (m : ℕ) (v : FreeGroup (Fin m)), v ≠ 1 → ∀ g : G,
    ∃ f : Fin m → G, FreeGroup.lift f v = g

/-- A group contains free groups of every finite rank.  This is the exact
subgroup-universality fragment needed to turn two conjugacy classes into
verbal completeness. -/
def ContainsEveryFiniteRankFreeGroup (G : Type*) [Group G] : Prop :=
  ∀ m : ℕ, ∃ ι : FreeGroup (Fin m) →* G, Function.Injective ι

/-- Evaluating a free word after conjugating every variable conjugates the
original value. -/
theorem lift_conj (m : ℕ) (v : FreeGroup (Fin m)) (f : Fin m → G) (a : G) :
    FreeGroup.lift (fun i ↦ a * f i * a⁻¹) v =
      a * FreeGroup.lift f v * a⁻¹ := by
  let c : G →* G :=
    { toFun := fun x ↦ a * x * a⁻¹
      map_one' := by group
      map_mul' := by intro x y; group }
  change FreeGroup.lift (fun i ↦ c (f i)) v = c (FreeGroup.lift f v)
  have hlift : FreeGroup.lift (fun i ↦ c (f i)) = c.comp (FreeGroup.lift f) := by
    apply FreeGroup.ext_hom
    intro i
    simp
  exact DFunLike.congr_fun hlift v

/-- **Two conjugacy classes plus internal free groups force every nontrivial
word map to be onto.**  A free subgroup supplies one nonidentity value of the
word.  Simultaneous conjugation then moves that value to an arbitrary
nonidentity target; the identity target is obtained by substituting ones. -/
theorem isVerballyComplete_of_twoConjugacyClasses
    (hcc : HasTwoConjugacyClasses G)
    (hfree : ContainsEveryFiniteRankFreeGroup G) :
    IsVerballyComplete G := by
  intro m v hv g
  by_cases hg : g = 1
  · refine ⟨fun _ ↦ 1, ?_⟩
    simpa [hg] using
      DFunLike.congr_fun
        (FreeGroup.ext_hom (FreeGroup.lift (fun _ : Fin m ↦ (1 : G)))
          1 (by simp)) v
  · obtain ⟨ι, hι⟩ := hfree m
    let f : Fin m → G := fun i ↦ ι (FreeGroup.of i)
    have hlift : FreeGroup.lift f = ι := by
      apply FreeGroup.ext_hom
      intro i
      simp [f]
    have hvalue : FreeGroup.lift f v ≠ 1 := by
      rw [hlift]
      intro h
      apply hv
      apply hι
      simpa using h
    obtain ⟨a, ha⟩ := isConj_iff.mp (hcc.2 _ g hvalue hg)
    refine ⟨fun i ↦ a * f i * a⁻¹, ?_⟩
    rw [lift_conj, ha]

/-- The definition is satisfiable: the trivial group is verbally complete.
This is a control on the definition, not an interesting example. -/
theorem isVerballyComplete_punit : IsVerballyComplete PUnit.{1} :=
  fun _ _ _ g ↦ ⟨fun _ ↦ g, Subsingleton.elim _ _⟩

/-! ### The two words -/

/-- A nonzero power of a free generator is nontrivial: its image under the
abelianization `FreeGroup (Fin 1) → Multiplicative ℤ` is `n`. -/
theorem of_pow_ne_one {n : ℕ} (hn : n ≠ 0) :
    (FreeGroup.of (0 : Fin 1)) ^ n ≠ 1 := by
  intro hcon
  set φ := FreeGroup.lift (fun _ : Fin 1 ↦ Multiplicative.ofAdd (1 : ℤ)) with hφ
  have himage : φ ((FreeGroup.of (0 : Fin 1)) ^ n) = φ 1 := by rw [hcon]
  rw [map_pow, map_one, hφ, FreeGroup.lift_apply_of, ← ofAdd_nsmul,
    ofAdd_eq_one] at himage
  simp only [nsmul_eq_mul, mul_one, Nat.cast_eq_zero] at himage
  exact hn himage

/-- The commutator of two free generators is nontrivial: it evaluates to a
nonidentity permutation of three points. -/
theorem commutatorElement_of_ne_one :
    ⁅FreeGroup.of (0 : Fin 2), FreeGroup.of (1 : Fin 2)⁆ ≠ 1 := by
  intro hcon
  set φ := FreeGroup.lift (fun i : Fin 2 ↦
    if i = 0 then Equiv.swap (0 : Fin 3) 1 else Equiv.swap (1 : Fin 3) 2) with hφ
  have himage : φ ⁅FreeGroup.of (0 : Fin 2), FreeGroup.of (1 : Fin 2)⁆ = φ 1 := by
    rw [hcon]
  rw [map_commutatorElement, map_one, hφ, FreeGroup.lift_apply_of,
    FreeGroup.lift_apply_of] at himage
  revert himage
  decide

/-! ### Consequences -/

namespace IsVerballyComplete

variable (h : IsVerballyComplete G)
include h

/-- Every nontrivial word map is surjective. -/
theorem wordMap_surjective {m : ℕ} {v : FreeGroup (Fin m)} (hv : v ≠ 1) :
    Function.Surjective (fun f : Fin m → G ↦ FreeGroup.lift f v) :=
  fun g ↦ h m v hv g

/-- **Divisibility.**  A verbally complete group is divisible: every
element is an `n`-th power for every `n ≥ 1`. -/
theorem exists_pow_eq {n : ℕ} (hn : n ≠ 0) (g : G) : ∃ x : G, x ^ n = g := by
  obtain ⟨f, hf⟩ := h 1 ((FreeGroup.of (0 : Fin 1)) ^ n) (of_pow_ne_one hn) g
  exact ⟨f 0, by rwa [map_pow, FreeGroup.lift_apply_of] at hf⟩

/-- **Commutator width one.**  Every element of a verbally complete group is a
single commutator, so the commutator width is one and the group is perfect. -/
theorem exists_commutatorElement_eq (g : G) : ∃ x y : G, ⁅x, y⁆ = g := by
  obtain ⟨f, hf⟩ := h 2 ⁅FreeGroup.of (0 : Fin 2), FreeGroup.of (1 : Fin 2)⁆
    commutatorElement_of_ne_one g
  refine ⟨f 0, f 1, ?_⟩
  rwa [map_commutatorElement, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of] at hf

/-- Commutator length one is inherited by every power, which is the estimate a
stable commutator length would be computed from: `cl (gⁿ) ≤ 1` for all `n`, so
`scl g = 0`. -/
theorem exists_commutatorElement_eq_pow (g : G) (n : ℕ) :
    ∃ x y : G, ⁅x, y⁆ = g ^ n := h.exists_commutatorElement_eq (g ^ n)

/-- In a two-conjugacy-class verbally complete group, every nonidentity
element is an `n`-th power of a conjugate of itself. -/
theorem exists_conj_pow_eq
    (hcc : HasTwoConjugacyClasses G) {n : ℕ} (hn : n ≠ 0)
    {g : G} (hg : g ≠ 1) :
    ∃ a : G, (a * g * a⁻¹) ^ n = g := by
  obtain ⟨x, hx⟩ := h.exists_pow_eq hn g
  have hx1 : x ≠ 1 := by
    intro hx1
    apply hg
    simpa [hx1] using hx.symm
  obtain ⟨a, ha⟩ := isConj_iff.mp (hcc.2 g x hg hx1)
  refine ⟨a, ?_⟩
  rw [ha, hx]

/-- In a two-conjugacy-class verbally complete group, every nonidentity
element is a commutator of two conjugates of itself. -/
theorem exists_commutatorElement_conj_eq
    (hcc : HasTwoConjugacyClasses G) {g : G} (hg : g ≠ 1) :
    ∃ a b : G, ⁅a * g * a⁻¹, b * g * b⁻¹⁆ = g := by
  obtain ⟨x, y, hxy⟩ := h.exists_commutatorElement_eq g
  have hx : x ≠ 1 := by
    intro hx
    apply hg
    simpa [hx] using hxy.symm
  have hy : y ≠ 1 := by
    intro hy
    apply hg
    simpa [hy] using hxy.symm
  obtain ⟨a, ha⟩ := isConj_iff.mp (hcc.2 g x hg hx)
  obtain ⟨b, hb⟩ := isConj_iff.mp (hcc.2 g y hg hy)
  exact ⟨a, b, by simpa [ha, hb] using hxy⟩

end IsVerballyComplete

end GroupApproximation.Monsters
