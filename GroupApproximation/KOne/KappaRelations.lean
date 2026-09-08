import GroupApproximation.KOne.UnstableKOneAbelian
import GroupApproximation.KOne.AlgebraicKOne
import GroupApproximation.Leavitt.FamilyDiagonalClass
import GroupApproximation.Meta.AxiomGuard

/-!
# What the canonical map `κ : Rˣ → K₁(R)` does over a strongly divisible ring

Two facts about `AlgebraicK.kappa`, both consequences of the rank-`n` Gaussian
elimination of `KOne/RankNElimination.lean`:

* **`kappa_surjective`** --- over a nontrivial ring with single-sandwich
  division, `κ : Rˣ → K₁(R)` is surjective.  Every class of `GL(R)` is
  represented at some finite rank, elimination carries that representative to
  `diagAt 0 u`, and `diagAt 0 u` is the stabilisation of `u ∈ GL₁(R)`.  This is
  the surjectivity clause of Ara--Goodearl--Pardo Theorem 2.4, for every
  strongly divisible ring and with no reference to that paper.

* **`kappa_central_pow_card_sub_one`** --- if `R` carries a complete matrix
  family on `ι`, then every **central** unit `c` satisfies

      `κ(c) ^ (|ι| - 1) = 1`   in `K₁(R)`.

  The proof is the corner decomposition `c = ∏ᵢ (1 + (c-1)pᵢ)` over the range
  idempotents of the family, together with the corner-insertion coset identity
  `StableUnitsGenerators.pairKappaUnit_mul_inv_mem_stableUnits`, which makes
  every factor `κ`-equal to `c` itself.  So `κ(c) = κ(c)^{|ι|}`.

## What this is for

`non_mf_groups_exist.tex`, `cor:leavitt-mf-quotient`, states
`K₁(L_k(1,d)) ≅ k^×/(k^×)^{d-1}` on Khanh--Thanh's authority.  The exponent
relation is the half of that identification which does **not** need the
citation: it is `kappa_central_pow_card_sub_one` at the `d`-ary Leavitt family,
where `|ι| = d`.  It says the composite `k^× → Rˣ → K₁(R)` kills `(k^×)^{d-1}`,
so it factors through `k^×/(k^×)^{d-1}`.

The two clauses of the identification that remain open after this file are
recorded, as named propositions with their exact content, in
`Manuscript/OneSidedMFRadical/LeavittKOneFormula.lean`.
-/

namespace GroupApproximation
namespace AlgebraicK

open MatrixDiagonalization RankNElimination

variable {R : Type*} [Ring R]

/-! ### The stabilisation of a `1 × 1` matrix is a `diagAt` -/

theorem unitsToGLOne_val_apply (u : Rˣ) (i j : Fin 1) :
    ((unitsToGLOne R u : (Matrix (Fin 1) (Fin 1) R)ˣ) : Matrix (Fin 1) (Fin 1) R)
        i j = (u : R) := by
  have hij : i = j := Subsingleton.elim i j
  subst hij
  show (Matrix.scalar (Fin 1) (u : R)) i i = (u : R)
  simp

theorem glStab_one_eq_diagAt (n : ℕ) (hn : 0 < n) (h1n : 1 ≤ n) (u : Rˣ) :
    glStab R 1 n h1n (unitsToGLOne R u) = diagAt (⟨0, hn⟩ : Fin n) u := by
  apply Units.ext
  rw [glStab_val, diagAt_val]
  ext x y
  rw [stabMatrix_apply, Matrix.diagonal_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl]
    by_cases hx : (x : ℕ) < 1
    · have hxval : (x : ℕ) = 0 := by omega
      have hx0 : x = (⟨0, hn⟩ : Fin n) := Fin.ext hxval
      rw [padEntry_of_lt_lt _ hx hx, if_pos hx0, unitsToGLOne_val_apply]
    · have hx0 : x ≠ (⟨0, hn⟩ : Fin n) := fun h ↦ hx (by rw [h]; exact Nat.zero_lt_one)
      rw [padEntry_diag_of_ge _ hx, if_neg hx0]
  · rw [if_neg hxy]
    by_cases hx : (x : ℕ) < 1
    · by_cases hy : (y : ℕ) < 1
      · exact absurd (Fin.ext (by omega) : x = y) hxy
      · rw [padEntry_of_lt_ge _ hx hy]
    · rw [padEntry_of_ge _ hx, if_neg (fun h ↦ hxy (Fin.ext h))]

/-- At rank two the stabilisation is the rank-two diagonal unit. -/
theorem glStab_one_two_eq_diagUnit (u : Rˣ) :
    glStab R 1 2 (by omega) (unitsToGLOne R u) = diagUnit u := by
  rw [glStab_one_eq_diagAt 2 (by omega) (by omega)]
  apply Units.ext
  rw [diagAt_val]
  show (Matrix.diagonal fun i ↦ if i = (⟨0, by omega⟩ : Fin 2) then (u : R)
    else 1) = !![(u : R), 0; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-! ### Stably elementary units are `κ`-trivial -/

/-- A unit whose `diag(u, 1)` is elementary is killed by `κ`. -/
theorem kappa_eq_one_of_mem_stableUnits {u : Rˣ} (hu : u ∈ stableUnits R) :
    kappa R u = 1 := by
  rw [kappa_eq_one_iff, ← glColimOf_glStab (R := R) (show 1 ≤ 2 by omega)
    (unitsToGLOne R u), glStab_one_two_eq_diagUnit]
  exact glColimOf_mem_elementaryColim (R := R) ((mem_stableUnits_iff u).mp hu)

/-- **The corner insertion does not move a `κ`-class.** -/
theorem kappa_pairKappaUnit [Nontrivial R]
    (hdiv : ∀ x : R, x ≠ 0 → ∃ p q : R, p * x * q = 1) (s t : R)
    (hts : t * s = 1) (u : Rˣ) :
    kappa R (pairKappaUnit s t hts u) = kappa R u := by
  have h := kappa_eq_one_of_mem_stableUnits
    (pairKappaUnit_mul_inv_mem_stableUnits s t hts hdiv u)
  rw [map_mul, map_inv, mul_inv_eq_one] at h
  exact h

/-! ### Surjectivity of `κ` -/

/-- **`κ : Rˣ → K₁(R)` is surjective** over a nontrivial ring with
single-sandwich division.  This is the surjectivity clause of
Ara--Goodearl--Pardo Theorem 2.4, proved here from Gaussian elimination
alone. -/
theorem kappa_surjective [Nontrivial R] (hdiv : HasSingleSandwichDivision R) :
    Function.Surjective (kappa R) := by
  intro z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨n, A, rfl⟩ := DirectLimit.exists_eq_mk (f := glStab R) x
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, ?_⟩
    have hA : A = 1 := by
      apply Units.ext
      ext i
      exact i.elim0
    rw [hA]
    show kappa R 1 = QuotientGroup.mk (glColimOf R 0 1)
    rw [map_one, map_one]
    exact (QuotientGroup.mk_one _).symm
  · obtain ⟨E, hE, F, hF, u, hEF⟩ :=
      exists_elementary_mul_diagAt hdiv A (⟨0, hn⟩ : Fin n)
    refine ⟨u, ?_⟩
    have hAeq : A = E⁻¹ * diagAt (⟨0, hn⟩ : Fin n) u * F⁻¹ := by
      rw [← hEF]; group
    have hmk : ∀ X ∈ elementaryGroup (Fin n) R,
        QuotientGroup.mk' (elementaryColim R) (glColimOf R n X) = 1 := fun X hX ↦
      (QuotientGroup.eq_one_iff _).mpr (glColimOf_mem_elementaryColim (R := R) hX)
    show kappa R u = QuotientGroup.mk' (elementaryColim R) (glColimOf R n A)
    rw [hAeq, map_mul, map_mul, map_mul, map_mul, hmk _ (inv_mem hE),
      hmk _ (inv_mem hF), one_mul, mul_one,
      ← glStab_one_eq_diagAt n hn (by omega) u,
      glColimOf_glStab (R := R) (show 1 ≤ n by omega)]
    rfl

/-! ### The exponent relation for central units -/

section Family

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The corner insertion of a unit at the `i`-th slot of a complete matrix
family. -/
def familyCorner (F : CompleteMatrixFamily R ι) (i : ι) (c : Rˣ) : Rˣ :=
  pairKappaUnit (F.left i) (F.right i) (F.right_mul_left_self i) c

theorem familyCorner_val (F : CompleteMatrixFamily R ι) (i : ι) (c : Rˣ)
    (hc : ∀ x : R, (c : R) * x = x * (c : R)) :
    (familyCorner F i c : R) = 1 + ((c : R) - 1) * (F.left i * F.right i) := by
  rw [familyCorner, pairKappaUnit_val, ← hc (F.left i)]
  noncomm_ring

theorem kappa_familyCorner [Nontrivial R]
    (hdiv : ∀ x : R, x ≠ 0 → ∃ p q : R, p * x * q = 1)
    (F : CompleteMatrixFamily R ι) (i : ι) (c : Rˣ) :
    kappa R (familyCorner F i c) = kappa R c :=
  kappa_pairKappaUnit hdiv _ _ _ c

/-- The partial corner products: over any finite set of slots, the product of
the corner insertions is a unit with the stated value and with `κ`-class the
`|S|`-th power of `κ c`. -/
theorem exists_partial_central [Nontrivial R]
    (hdiv : ∀ x : R, x ≠ 0 → ∃ p q : R, p * x * q = 1)
    (F : CompleteMatrixFamily R ι) (c : Rˣ)
    (hc : ∀ x : R, (c : R) * x = x * (c : R)) :
    ∀ S : Finset ι, ∃ w : Rˣ,
      (w : R) = 1 + ((c : R) - 1) * ∑ i ∈ S, F.left i * F.right i ∧
        kappa R w = kappa R c ^ S.card := by
  classical
  have hc1 : ∀ x : R, ((c : R) - 1) * x = x * ((c : R) - 1) := by
    intro x
    rw [sub_mul, one_mul, mul_sub, mul_one, hc x]
  intro S
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | insert a S haS IH =>
      obtain ⟨w, hwval, hwk⟩ := IH
      have hz : (F.left a * F.right a) *
          (∑ i ∈ S, F.left i * F.right i) = 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_eq_zero fun i hi ↦ ?_
        have hai : a ≠ i := fun h ↦ haS (by rw [h]; exact hi)
        calc F.left a * F.right a * (F.left i * F.right i)
            = F.left a * (F.right a * F.left i) * F.right i := by noncomm_ring
          _ = 0 := by rw [F.right_mul_left_ne hai, mul_zero, zero_mul]
      refine ⟨familyCorner F a c * w, ?_, ?_⟩
      · rw [Units.val_mul, familyCorner_val F a c hc, hwval,
          Finset.sum_insert haS]
        have hcross : (((c : R) - 1) * (F.left a * F.right a)) *
            (((c : R) - 1) * ∑ i ∈ S, F.left i * F.right i) = 0 := by
          calc (((c : R) - 1) * (F.left a * F.right a)) *
                (((c : R) - 1) * ∑ i ∈ S, F.left i * F.right i)
              = ((c : R) - 1) * ((F.left a * F.right a) * ((c : R) - 1)) *
                  (∑ i ∈ S, F.left i * F.right i) := by noncomm_ring
            _ = ((c : R) - 1) * (((c : R) - 1) * (F.left a * F.right a)) *
                  (∑ i ∈ S, F.left i * F.right i) := by
                rw [← hc1 (F.left a * F.right a)]
            _ = ((c : R) - 1) * ((c : R) - 1) *
                  ((F.left a * F.right a) * ∑ i ∈ S, F.left i * F.right i) := by
                noncomm_ring
            _ = 0 := by rw [hz, mul_zero]
        calc (1 + ((c : R) - 1) * (F.left a * F.right a)) *
              (1 + ((c : R) - 1) * ∑ i ∈ S, F.left i * F.right i)
            = 1 + ((c : R) - 1) * (F.left a * F.right a) +
                ((c : R) - 1) * (∑ i ∈ S, F.left i * F.right i) +
                (((c : R) - 1) * (F.left a * F.right a)) *
                  (((c : R) - 1) * ∑ i ∈ S, F.left i * F.right i) := by
              noncomm_ring
          _ = 1 + ((c : R) - 1) *
                (F.left a * F.right a + ∑ i ∈ S, F.left i * F.right i) := by
              rw [hcross, add_zero]
              noncomm_ring
      · rw [map_mul, hwk, kappa_familyCorner hdiv F a c,
          Finset.card_insert_of_notMem haS, pow_succ]
        exact mul_comm _ _

/-- **`κ(c) = κ(c)^{|ι|}` for a central unit.**  The corner decomposition of a
central unit along a complete matrix family has `|ι|` factors, each of them
`κ`-equal to the unit itself. -/
theorem kappa_central_eq_pow [Nontrivial R]
    (hdiv : ∀ x : R, x ≠ 0 → ∃ p q : R, p * x * q = 1)
    (F : CompleteMatrixFamily R ι) (c : Rˣ)
    (hc : ∀ x : R, (c : R) * x = x * (c : R)) :
    kappa R c = kappa R c ^ Fintype.card ι := by
  obtain ⟨w, hwval, hwk⟩ := exists_partial_central hdiv F c hc Finset.univ
  have hwc : w = c := by
    apply Units.ext
    rw [hwval, F.complete, mul_one]
    noncomm_ring
  rw [hwc] at hwk
  rw [Finset.card_univ] at hwk
  exact hwk

/-- **The exponent relation.**  A central unit of a ring carrying a complete
matrix family on `ι` has `κ`-class of order dividing `|ι| - 1`. -/
theorem kappa_central_pow_card_sub_one [Nontrivial R]
    (hdiv : ∀ x : R, x ≠ 0 → ∃ p q : R, p * x * q = 1)
    (F : CompleteMatrixFamily R ι) (c : Rˣ)
    (hc : ∀ x : R, (c : R) * x = x * (c : R)) :
    kappa R c ^ (Fintype.card ι - 1) = 1 := by
  have h := kappa_central_eq_pow hdiv F c hc
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
  · rw [h0]
    simp
  · have hsplit : Fintype.card ι = (Fintype.card ι - 1) + 1 := by omega
    rw [hsplit, pow_succ] at h
    have hcancel : (1 : AlgebraicKOne R) * kappa R c =
        kappa R c ^ (Fintype.card ι - 1) * kappa R c := by
      rw [one_mul]
      exact h
    exact (mul_right_cancel hcancel).symm

end Family

end AlgebraicK
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.AlgebraicK.kappa_surjective
#audit_axioms GroupApproximation.AlgebraicK.kappa_eq_one_of_mem_stableUnits
#audit_axioms GroupApproximation.AlgebraicK.kappa_central_pow_card_sub_one
