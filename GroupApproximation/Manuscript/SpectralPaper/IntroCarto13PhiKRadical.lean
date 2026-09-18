import GroupApproximation.Manuscript.SpectralPaper.IntroCarto13PhiKKernel
import GroupApproximation.Manuscript.NonMFNotes.Full.VisibleQuotient.TorsionTelescope
import GroupApproximation.Manuscript.NonMFNotes.Full.VisibleQuotient.LamplighterRF
import GroupApproximation.Analysis.PeterWeylSeparation
import Mathlib.GroupTheory.Abelianization.Finite
import GroupApproximation.Meta.AxiomGuard

/-!
# `ker Φ_K` is every radical, for every finite lamp group

Notes census, `thm:notes-visible-quotient` (`non_mf_group_notes.tex` ~1966):

> Moreover `ker Φ_K = Rad_MF = Rad_fd = Res_fin = Rad_lin = Rad_Bohr`.

Route.
1. *Spectral motion.*  Take two sites `v • root` and `w • root` of equal
   height.  `NN04.lampDiff_mem_actualCoronaMFResidual_of_rightHom_eq_of_pow`
   puts their lamp difference in the corona MF radical.  The inputs are the
   Kazhdan base `Γ̄` and the finite order of the lamp value
   (`orderOf_pos`, `pow_orderOf_eq_one`).
2. *Fibre collapse.*  `NN04.ker_pushWreath_comp_le` with `R = Rad_MF` gives
   `ker Φ_K ≤ Rad_MF`.  Its fibre hypothesis is `exists_second_site`.
3. *Residual finiteness of the target.*  `P_K = K_ab^(G_*/ker h) ⋊ G_*` is
   residually finite by `NN04.wreath_quotient_isResiduallyFinite` over the
   residually finite `G_*`.
4. *Coincidence.*  `five_radicals_eq` with Peter–Weyl separation
   (`PeterWeyl.separatesPoints`) gives all five equalities.

No perfectness of `K` is used anywhere.
-/

namespace GroupApproximation.SpectralPaper.IntroCarto13

open SemidirectProduct MarkedCompression ExplicitLinearModel LiteralDoublingWreath
open FinitePerfectLamp GroupApproximation.WreathLampPushforward GroupApproximation.Full.NN04
open MatricialStabilityRadical

/-- **Spectral motion.**  Every equal-height difference is invisible to every
corona representation. -/
theorem heightDiff_mem_actualCoronaMFResidual (K : Type) [Group K] [Finite K]
    {y y' : Cosets conjD conjD_injective} (h : heightSite y = heightSite y') (k : K) :
    (inl (Lamp.single y k * (Lamp.single y' k)⁻¹) : WFin K) ∈
      actualCoronaMFResidual (WFin K) := by
  revert h
  refine QuotientGroup.induction_on y fun v => ?_
  refine QuotientGroup.induction_on y' fun w => ?_
  intro h
  have hvw : (SemidirectProduct.rightHom : GStar →* Multiplicative ℤ) v =
      SemidirectProduct.rightHom w := by
    have h' : (QuotientGroup.mk v : HeightSites) = QuotientGroup.mk w := h
    rw [QuotientGroup.eq, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h'
    exact h'
  have hmem := lampDiff_mem_actualCoronaMFResidual_of_rightHom_eq_of_pow conjD
    conjD_injective CommutingLampCollapse.gammaBar_hasKazhdanPropertyT (orderOf_pos k)
    (pow_orderOf_eq_one k) hvw
  rw [smul_rootCoset, smul_rootCoset] at hmem
  exact hmem

#audit_axioms GroupApproximation.SpectralPaper.IntroCarto13.heightDiff_mem_actualCoronaMFResidual

/-- **`ker Φ_K ≤ Rad_MF`.** -/
theorem ker_heightAbelianization_le_actualCoronaMFResidual (K : Type) [Group K]
    [Finite K] :
    (heightAbelianization K).ker ≤ actualCoronaMFResidual (WFin K) :=
  ker_pushWreath_comp_le (actualCoronaMFResidual (WFin K)) heightSite heightSite_smul
    (fun _ _ k h => heightDiff_mem_actualCoronaMFResidual K h k) exists_second_site

#audit_axioms GroupApproximation.SpectralPaper.IntroCarto13.ker_heightAbelianization_le_actualCoronaMFResidual

/-- The visible quotient is residually finite. -/
theorem heightLampQuotient_isResiduallyFinite (K : Type) [Group K] [Finite K] :
    IsResiduallyFinite (heightLampQuotient K) :=
  wreath_quotient_isResiduallyFinite (A := Abelianization K)
    AlternatingLampFamily.vertical_isResiduallyFinite
    (SemidirectProduct.rightHom : GStar →* Multiplicative ℤ)

#audit_axioms GroupApproximation.SpectralPaper.IntroCarto13.heightLampQuotient_isResiduallyFinite

/-- **Five radicals, for every finite lamp group.**
`Rad_MF = Rad_fd = Res_fin = Rad_lin = Rad_Bohr = ker Φ_K`. -/
theorem five_radicals_eq_ker_heightAbelianization (K : Type) [Group K] [Finite K] :
    actualCoronaMFResidual (WFin K) = (heightAbelianization K).ker ∧
      fdUnitaryResidual (WFin K) = (heightAbelianization K).ker ∧
        finiteResidual (WFin K) = (heightAbelianization K).ker ∧
          linearResidual (WFin K) = (heightAbelianization K).ker ∧
            PeterWeyl.bohrResidual (WFin K) = (heightAbelianization K).ker :=
  five_radicals_eq PeterWeyl.separatesPoints (heightAbelianization K)
    (heightLampQuotient_isResiduallyFinite K)
    (ker_heightAbelianization_le_actualCoronaMFResidual K)

#audit_axioms GroupApproximation.SpectralPaper.IntroCarto13.five_radicals_eq_ker_heightAbelianization

end GroupApproximation.SpectralPaper.IntroCarto13
