import GroupApproximation.KOne.MoritaKOne
import GroupApproximation.KOne.LeavittKOneFamilyPower
import GroupApproximation.KOne.KappaRelations
import GroupApproximation.Leavitt.FamilyDescent
import GroupApproximation.Leavitt.AryPurelyInfinite
import GroupApproximation.Meta.AxiomGuard

/-!
# `E_∞(R)` is a directed union, and stable `K₁` is the unstable Whitehead
quotient

`non_mf_groups_exist.tex`, `cor:leavitt-mf-quotient` (tex line 1249):

> `H/EL_d(R) ≅ K₁(R) ≅ k^×/(k^×)^{d-1}`

The census records the **first** of those isomorphisms as uncarried
(`6aef426dfc7a`, unassigned): the tree names `K₁(R)` as the direct limit
`GL(R)/E_∞(R)` and names `H/EL_d(R)` as an unstable quotient, and nothing
compares them.  This module proves the comparison in Whitehead form,

    `K₁(R) ≅ R^× / stableUnits R`     (`aryLeavitt_algebraicKOne_equiv`)

for `R = L_k(1,d)` at every field `k` and every `d ≥ 2`, where
`stableUnits R = {u : diag(u,1) ∈ EL₂(R)}` is the tree's rank-two Whitehead
subgroup.  Equivalently `ker κ = stableUnits R`, the reverse of the inclusion
`kappa_eq_one_of_mem_stableUnits` already on the tree.
`KOne/LeavittKOneUnstableComparison.lean` turns it into the printed form.

## Why it was blocked, and what unblocks it

`κ u = 1` says the class of `diag(u, 1, …)` is trivial in `GL(R)/E_∞(R)`, and
`E_∞(R)` is a *supremum* of the images of the `EL_n(R)`, so on its face this
gives a product of elementary classes at various ranks rather than a single
rank.  Two things were missing.

* Directedness.  `AlgebraicK.glStab_elementaryGroup_le` (`KOne/MoritaKOne.lean`)
  says padding preserves elementary matrices, so the images increase and the
  supremum is a union: `mem_elementaryColim_iff` below, and `u` is elementary at
  one rank `n`.
* A complete matrix family at a rank `≥ n`.  `AryLeavitt.family` lives at rank
  `d` only, and `n` is not ours to choose; `KOne/LeavittKOneFamilyPower.lean`
  supplies families at the cofinal ranks `dⁿ`.

With both, the class is pushed to a rank `dʲ ≥ n` carrying a family, and
`CompleteMatrixFamily.mem_stableUnits_of_cornerDiag_mem` descends it to
`stableUnits R`.

## Generality

The general-ring statements hold for an arbitrary nontrivial ring with
single-sandwich division carrying complete matrix families at cofinal ranks;
only the last three theorems mention the Leavitt algebra.
-/

namespace GroupApproximation
namespace KOneDescent

open AlgebraicK MatrixDiagonalization RankNElimination

variable {R : Type*} [Ring R]

/-! ### `E_∞(R)` is a directed union -/

/-- The images of the finite-rank elementary groups increase with the rank. -/
theorem elementaryImage_mono {n m : ℕ} (h : n ≤ m) :
    (elementaryGroup (Fin n) R).map (glColimOf R n)
      ≤ (elementaryGroup (Fin m) R).map (glColimOf R m) := by
  rintro x hx
  rw [Subgroup.mem_map] at hx ⊢
  obtain ⟨u, hu, rfl⟩ := hx
  refine ⟨glStab R n m h u, ?_, glColimOf_glStab (R := R) h u⟩
  exact glStab_elementaryGroup_le h (Subgroup.mem_map_of_mem _ hu)

/-- **A trivial class is elementary at one finite rank.**  `E_∞(R)` is the
directed union of the images of the `EL_n(R)`, not merely the subgroup they
generate. -/
theorem mem_elementaryColim_iff (x : ClassicalGLColim R) :
    x ∈ elementaryColim R ↔
      ∃ n : ℕ, x ∈ (elementaryGroup (Fin n) R).map (glColimOf R n) := by
  show x ∈ (⨆ n : ℕ, (elementaryGroup (Fin n) R).map (glColimOf R n)) ↔ _
  exact Subgroup.mem_iSup_of_directed (fun n m ↦
    ⟨max n m, elementaryImage_mono (le_max_left n m),
      elementaryImage_mono (le_max_right n m)⟩)

/-! ### The kernel of `κ` -/

/-- **`κ u = 1` exactly when `u` is stably elementary at rank two.**

The `←` direction is the tree's `kappa_eq_one_of_mem_stableUnits`.  The `→`
direction is the content: directedness gives a single rank, cofinality of the
family ranks gives a rank with a complete matrix family above it, and the
family descends the class. -/
theorem kappa_eq_one_iff_mem_stableUnits [Nontrivial R]
    (hdiv : ∀ x : R, x ≠ 0 → ∃ p q : R, p * x * q = 1)
    (hfam : ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ Nonempty (CompleteMatrixFamily R (Fin m)))
    (u : Rˣ) : kappa R u = 1 ↔ u ∈ stableUnits R := by
  refine ⟨fun hu ↦ ?_, fun hu ↦ kappa_eq_one_of_mem_stableUnits hu⟩
  rw [kappa_eq_one_iff] at hu
  obtain ⟨n, hn⟩ := (mem_elementaryColim_iff _).mp hu
  rw [Subgroup.mem_map] at hn
  obtain ⟨v, hv, hvx⟩ := hn
  have hmk : (⟦⟨n, v⟩⟧ : ClassicalGLColim R)
      = ⟦⟨1, unitsToGLOne R u⟩⟧ := hvx
  obtain ⟨i, hni, h1i, heq⟩ := Quotient.exact hmk
  obtain ⟨m, him, ⟨F⟩⟩ := hfam i
  have hnm : n ≤ m := hni.trans him
  have h1m : 1 ≤ m := h1i.trans him
  have hpadv : glStab R n m hnm v ∈ elementaryGroup (Fin m) R :=
    glStab_elementaryGroup_le hnm (Subgroup.mem_map_of_mem _ hv)
  have hpadeq : glStab R n m hnm v = glStab R 1 m h1m (unitsToGLOne R u) := by
    rw [← glStab_glStab R hni him hnm, ← glStab_glStab R h1i him h1m, heq]
  have hm0 : 0 < m := lt_of_lt_of_le Nat.zero_lt_one h1m
  have hdiag : diagAt (⟨0, hm0⟩ : Fin m) u ∈ elementaryGroup (Fin m) R := by
    rw [← glStab_one_eq_diagAt m hm0 h1m u, ← hpadeq]
    exact hpadv
  have hcorner : CompleteMatrixFamily.cornerDiagUnit (⟨0, hm0⟩ : Fin m) u
      ∈ elementaryGroup (Fin m) R := by
    have hval : CompleteMatrixFamily.cornerDiagUnit (⟨0, hm0⟩ : Fin m) u
        = diagAt (⟨0, hm0⟩ : Fin m) u := Units.ext rfl
    rw [hval]
    exact hdiag
  exact F.mem_stableUnits_of_cornerDiag_mem hdiv (⟨0, hm0⟩ : Fin m) u hcorner

/-- **Stable `K₁` is the rank-two Whitehead quotient.** -/
theorem algebraicKOne_equiv_stableQuotient [Nontrivial R]
    (hdiv : ∀ x : R, x ≠ 0 → ∃ p q : R, p * x * q = 1)
    (hfam : ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ Nonempty (CompleteMatrixFamily R (Fin m))) :
    Nonempty (AlgebraicKOne R ≃* (Rˣ ⧸ stableUnits R)) := by
  have hker : (kappa R).ker = stableUnits R := by
    ext w
    rw [MonoidHom.mem_ker]
    exact kappa_eq_one_iff_mem_stableUnits hdiv hfam w
  exact ⟨((QuotientGroup.quotientKerEquivOfSurjective (kappa R)
    (kappa_surjective hdiv)).symm).trans
      (QuotientGroup.quotientMulEquivOfEq hker)⟩

/-! ### The Leavitt algebra -/

open AryLeavitt

/-- Complete matrix families over `L_k(1,d)` at cofinal ranks: the ranks `dⁿ`.
-/
theorem aryLeavitt_families_cofinal (k : Type) [Field k] (d : ℕ) (hd : 2 ≤ d) :
    ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧
      Nonempty (CompleteMatrixFamily (AryLeavittAlgebra k d) (Fin m)) := by
  intro n
  obtain ⟨j, hj⟩ := CompleteMatrixFamily.exists_pow_ge hd n
  exact ⟨d ^ j, hj, ⟨(AryLeavitt.family k d).pow j⟩⟩

/-- **`K₁(L_k(1,d)) ≅ L_k(1,d)^× / stableUnits`**, at every field and every
`d ≥ 2`: the stable `K₁` of the manuscript's ring is its unstable rank-two
Whitehead quotient. -/
theorem aryLeavitt_algebraicKOne_equiv (k : Type) [Field k] (d : ℕ) (hd : 2 ≤ d) :
    Nonempty (AlgebraicKOne (AryLeavittAlgebra k d) ≃*
      ((AryLeavittAlgebra k d)ˣ ⧸ stableUnits (AryLeavittAlgebra k d))) := by
  haveI : NeZero d := ⟨by omega⟩
  exact algebraicKOne_equiv_stableQuotient
    (AryLeavitt.hasSingleSandwichDivision k d hd)
    (aryLeavitt_families_cofinal k d hd)

/-- **`ker κ = stableUnits`** for `L_k(1,d)`, the form the unstable comparison
consumes. -/
theorem aryLeavitt_kappa_ker (k : Type) [Field k] (d : ℕ) (hd : 2 ≤ d) :
    (kappa (AryLeavittAlgebra k d)).ker = stableUnits (AryLeavittAlgebra k d) := by
  haveI : NeZero d := ⟨by omega⟩
  ext w
  rw [MonoidHom.mem_ker]
  exact kappa_eq_one_iff_mem_stableUnits
    (AryLeavitt.hasSingleSandwichDivision k d hd)
    (aryLeavitt_families_cofinal k d hd) w

end KOneDescent
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.KOneDescent.elementaryImage_mono
#audit_axioms GroupApproximation.KOneDescent.mem_elementaryColim_iff
#audit_axioms GroupApproximation.KOneDescent.kappa_eq_one_iff_mem_stableUnits
#audit_axioms GroupApproximation.KOneDescent.algebraicKOne_equiv_stableQuotient
#audit_axioms GroupApproximation.KOneDescent.aryLeavitt_families_cofinal
#audit_axioms GroupApproximation.KOneDescent.aryLeavitt_algebraicKOne_equiv
#audit_axioms GroupApproximation.KOneDescent.aryLeavitt_kappa_ker
