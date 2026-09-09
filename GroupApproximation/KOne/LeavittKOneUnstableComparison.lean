import GroupApproximation.KOne.LeavittKOneWhitehead
import GroupApproximation.KOne.LeavittKOneScalarSurjectivity
import GroupApproximation.Meta.AxiomGuard

/-!
# `GL_d(R)/EL_d(R) ≅ K₁(R)`: the first printed isomorphism

`non_mf_groups_exist.tex`, `cor:leavitt-mf-quotient` (tex line 1249):

> `H/EL_d(R) ≅ K₁(R) ≅ k^×/(k^×)^{d-1}`

with `H = R^×` identified with `GL_d(R)`.  The census records the **first**
isomorphism as unassigned (`6aef426dfc7a`): the tree defines `K₁(R)` as the
direct limit `GL(R)/E_∞(R)` and `H/EL_d(R)` as an unstable quotient, and
nothing compared them.  This module proves the comparison, at every rank `n ≥ 2`
carrying a complete matrix family and in particular at `n = d` for
`R = L_k(1,d)`.

## The proof

`κ ∘ unitsEquiv : GL_n(R) → K₁(R)` is surjective because `κ` is.  Its kernel is
`EL_n(R)`:

* `EL_n(R) ≤ ker` is `AlgebraicK.kappa_unitsEquiv_elementary`
  (`KOne/LeavittKOneScalarSurjectivity.lean`): through the family an elementary
  matrix lands in `stableUnits R`, which `κ` kills.
* `ker ≤ EL_n(R)` is the content.  Rank-`n` Gaussian elimination writes
  `A = E⁻¹ · diagAt 0 w · F⁻¹` with `E, F` elementary, and the two elementary
  factors do not move the `κ`-class, so `κ w = 1`.  Then
  `KOne/LeavittKOneWhitehead.lean` gives `w ∈ stableUnits R`, i.e.
  `diag(w,1) ∈ EL₂(R)`, and **padding** (`AlgebraicK.glStab_elementaryGroup_le`,
  `KOne/MoritaKOne.lean`) carries that to `diagAt 0 w ∈ EL_n(R)`.  Hence
  `A ∈ EL_n(R)`.

The last step is what was missing before: the rank-two Whitehead subgroup and
the rank-`n` elementary group are compared by the block padding, and padding was
not known to preserve elementary matrices.

## Relation to Ara--Goodearl--Pardo

`MFQuotientUnitsKappaProof.agpUnitKappa` proves `ker κ = ⁅R^×, R^×⁆` for every
**countable** purely infinite simple ring, and with the tree's
`⁅GL_d(R), GL_d(R)⁆ = EL_d(R)` that already gives this isomorphism when `k` is
countable.  What is new here is the hypothesis, not the shape: the kernel is
computed as `stableUnits R` by `KOne/LeavittKOneWhitehead.lean`, which needs no
countability, so the comparison below holds at **every** field.  The two
together say `stableUnits R = ⁅R^×, R^×⁆` for countable `k`.

## What is still not the printed sentence

The printed display also has `H ≅ GL_d(R)`, which is
`LeavittMFQuotientGeneral.unitsEquivGL` and already on the tree, and the second
isomorphism `K₁(R) ≅ k^×/(k^×)^{d-1}`, which is open through
`LeavittKOneFormula.ScalarKernel`.
-/

namespace GroupApproximation
namespace KOneDescent

open AlgebraicK MatrixDiagonalization RankNElimination

variable {R : Type*} [Ring R]

/-! ### The rank-two Whitehead subgroup sits inside every higher elementary
group -/

/-- `diagAt` and the family's single-slot corner diagonal are the same unit. -/
theorem diagAt_eq_cornerDiagUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (l : ι) (u : Rˣ) :
    diagAt l u = CompleteMatrixFamily.cornerDiagUnit l u := Units.ext rfl

/-- **A stably elementary unit is elementary at every rank `n ≥ 2`.**  Padding
`diag(u,1)` from rank two to rank `n` gives `diagAt 0 u`, and padding preserves
elementary matrices. -/
theorem diagAt_mem_elementaryGroup_of_mem_stableUnits {n : ℕ} (h2n : 2 ≤ n)
    (hn0 : 0 < n) {u : Rˣ} (hu : u ∈ stableUnits R) :
    diagAt (⟨0, hn0⟩ : Fin n) u ∈ elementaryGroup (Fin n) R := by
  have h12 : (1 : ℕ) ≤ 2 := by omega
  have h1n : (1 : ℕ) ≤ n := by omega
  have hpad : glStab R 2 n h2n (diagUnit u) ∈ elementaryGroup (Fin n) R :=
    glStab_elementaryGroup_le h2n
      (Subgroup.mem_map_of_mem _ ((mem_stableUnits_iff u).mp hu))
  rwa [← glStab_one_two_eq_diagUnit u, glStab_glStab R h12 h2n h1n,
    glStab_one_eq_diagAt n hn0 h1n] at hpad

/-! ### The kernel of the comparison map -/

/-- **`ker (κ ∘ unitsEquiv) ≤ EL_n(R)`.** -/
theorem mem_elementaryGroup_of_kappa_unitsEquiv_eq_one {n : ℕ} (h2n : 2 ≤ n)
    [Nontrivial R] (hdiv : HasSingleSandwichDivision R)
    (F : CompleteMatrixFamily R (Fin n))
    (hker : ∀ w : Rˣ, kappa R w = 1 → w ∈ stableUnits R)
    {A : (Matrix (Fin n) (Fin n) R)ˣ} (hA : kappa R (F.unitsEquiv A) = 1) :
    A ∈ elementaryGroup (Fin n) R := by
  have hn0 : 0 < n := by omega
  obtain ⟨E, hE, G, hG, w, hEG⟩ :=
    exists_elementary_mul_diagAt hdiv A (⟨0, hn0⟩ : Fin n)
  have hAeq : A = E⁻¹ * diagAt (⟨0, hn0⟩ : Fin n) w * G⁻¹ := by
    rw [← hEG]
    group
  have hsplit : F.unitsEquiv A
      = F.unitsEquiv E⁻¹ * F.unitsEquiv (diagAt (⟨0, hn0⟩ : Fin n) w)
        * F.unitsEquiv G⁻¹ := by
    rw [hAeq, map_mul, map_mul]
  have hclass : kappa R (F.unitsEquiv A) = kappa R w := by
    rw [hsplit, map_mul, map_mul,
      kappa_unitsEquiv_elementary F (inv_mem hE),
      kappa_unitsEquiv_elementary F (inv_mem hG), one_mul, mul_one,
      diagAt_eq_cornerDiagUnit]
    exact kappa_unitsEquiv_cornerDiagUnit hdiv F (⟨0, hn0⟩ : Fin n) w
  have hkw : kappa R w = 1 := by rw [← hclass]; exact hA
  rw [hAeq]
  exact mul_mem (mul_mem (inv_mem hE)
    (diagAt_mem_elementaryGroup_of_mem_stableUnits h2n hn0 (hker w hkw)))
    (inv_mem hG)

/-- **The kernel of the comparison map is exactly `EL_n(R)`.** -/
theorem kappa_comp_unitsEquiv_ker {n : ℕ} (h2n : 2 ≤ n)
    [Nontrivial R] (hdiv : HasSingleSandwichDivision R)
    (F : CompleteMatrixFamily R (Fin n))
    (hker : ∀ w : Rˣ, kappa R w = 1 → w ∈ stableUnits R) :
    ((kappa R).comp F.unitsEquiv.toMonoidHom).ker = elementaryGroup (Fin n) R := by
  ext A
  rw [MonoidHom.mem_ker]
  exact ⟨fun hA ↦
      mem_elementaryGroup_of_kappa_unitsEquiv_eq_one h2n hdiv F hker hA,
    fun hA ↦ kappa_unitsEquiv_elementary F hA⟩

/-- **The printed first isomorphism, for an arbitrary ring with the two
inputs.**  `GL_n(R)/EL_n(R) ≅ K₁(R)` at any rank `n ≥ 2` carrying a complete
matrix family, over a nontrivial ring with single-sandwich division whose
`κ`-kernel is the rank-two Whitehead subgroup. -/
theorem unstableQuotient_equiv_algebraicKOne {n : ℕ} (h2n : 2 ≤ n)
    [Nontrivial R] (hdiv : HasSingleSandwichDivision R)
    (F : CompleteMatrixFamily R (Fin n))
    (hker : ∀ w : Rˣ, kappa R w = 1 → w ∈ stableUnits R)
    [(elementaryGroup (Fin n) R).Normal] :
    Nonempty (((Matrix (Fin n) (Fin n) R)ˣ ⧸ elementaryGroup (Fin n) R) ≃*
      AlgebraicKOne R) := by
  have hkereq := kappa_comp_unitsEquiv_ker h2n hdiv F hker
  have hsurj : Function.Surjective ((kappa R).comp F.unitsEquiv.toMonoidHom) := by
    intro z
    obtain ⟨w, hw⟩ := kappa_surjective hdiv z
    refine ⟨F.unitsEquiv.symm w, ?_⟩
    show kappa R (F.unitsEquiv (F.unitsEquiv.symm w)) = z
    rw [MulEquiv.apply_symm_apply]
    exact hw
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hkereq).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hsurj)⟩

/-! ### The Leavitt algebra -/

open AryLeavitt

/-- **The comparison map's kernel is `EL_d(R)`, for `R = L_k(1,d)`**, at every
field `k` and every `d ≥ 2`.  Stated without the quotient so that it needs no
normality instance. -/
theorem aryLeavitt_kappa_comp_unitsEquiv_ker (k : Type) [Field k] (d : ℕ)
    (hd : 2 ≤ d) :
    ((kappa (AryLeavittAlgebra k d)).comp
        (AryLeavitt.family k d).unitsEquiv.toMonoidHom).ker
      = elementaryGroup (Fin d) (AryLeavittAlgebra k d) := by
  haveI : NeZero d := ⟨by omega⟩
  exact kappa_comp_unitsEquiv_ker hd
    (AryLeavitt.hasSingleSandwichDivision k d hd) (AryLeavitt.family k d)
    (fun w hw ↦ (kappa_eq_one_iff_mem_stableUnits
      (AryLeavitt.hasSingleSandwichDivision k d hd)
      (aryLeavitt_families_cofinal k d hd) w).mp hw)

/-- **`EL_d(L_k(1,d))` is normal in `GL_d(L_k(1,d))`**, the instance the printed
quotient needs.  It is a theorem, not an assumption: single-sandwich division
gives it. -/
theorem aryLeavitt_elementaryGroup_normal (k : Type) [Field k] (d : ℕ)
    (hd : 2 ≤ d) :
    haveI : NeZero d := ⟨by omega⟩
    (elementaryGroup (Fin d) (AryLeavittAlgebra k d)).Normal := by
  haveI : NeZero d := ⟨by omega⟩
  exact elementaryGroup_normal_of_division
    (AryLeavitt.hasSingleSandwichDivision k d hd) (⟨0, by omega⟩ : Fin d)

/-- **The printed first isomorphism `GL_d(R)/EL_d(R) ≅ K₁(R)` for
`R = L_k(1,d)`**, at every field `k` and every `d ≥ 2`.

The two `haveI`s in the statement are not hypotheses: `NeZero d` and the
normality of `EL_d(R)` are both consequences of `hd`, supplied here because the
quotient type cannot be written down without them. -/
theorem aryLeavitt_unstableQuotient_equiv (k : Type) [Field k] (d : ℕ)
    (hd : 2 ≤ d) :
    haveI : NeZero d := ⟨by omega⟩
    haveI : (elementaryGroup (Fin d) (AryLeavittAlgebra k d)).Normal :=
      elementaryGroup_normal_of_division
        (AryLeavitt.hasSingleSandwichDivision k d hd) (⟨0, by omega⟩ : Fin d)
    Nonempty ((((Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ) ⧸
        elementaryGroup (Fin d) (AryLeavittAlgebra k d)) ≃*
      AlgebraicKOne (AryLeavittAlgebra k d)) := by
  haveI : NeZero d := ⟨by omega⟩
  haveI : (elementaryGroup (Fin d) (AryLeavittAlgebra k d)).Normal :=
    elementaryGroup_normal_of_division
      (AryLeavitt.hasSingleSandwichDivision k d hd) (⟨0, by omega⟩ : Fin d)
  exact unstableQuotient_equiv_algebraicKOne hd
    (AryLeavitt.hasSingleSandwichDivision k d hd) (AryLeavitt.family k d)
    (fun w hw ↦ (kappa_eq_one_iff_mem_stableUnits
      (AryLeavitt.hasSingleSandwichDivision k d hd)
      (aryLeavitt_families_cofinal k d hd) w).mp hw)

end KOneDescent
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.KOneDescent.diagAt_mem_elementaryGroup_of_mem_stableUnits
#audit_axioms
  GroupApproximation.KOneDescent.mem_elementaryGroup_of_kappa_unitsEquiv_eq_one
#audit_axioms GroupApproximation.KOneDescent.unstableQuotient_equiv_algebraicKOne
#audit_axioms GroupApproximation.KOneDescent.aryLeavitt_kappa_comp_unitsEquiv_ker
#audit_axioms GroupApproximation.KOneDescent.aryLeavitt_elementaryGroup_normal
#audit_axioms GroupApproximation.KOneDescent.aryLeavitt_unstableQuotient_equiv
