import GroupApproximation.Manuscript.NonMF.FreeNormalSubgroupSlice
import GroupApproximation.GGT.WPDElementaryEmbedding

/-!
# DGO 2.35 at the printed hypothesis, from named geometry

`FreeNormalSubgroupSlice` opened Dahmani--Guirardel--Osin's geometric residue
along their steps 1 to 3 and proved step 3.  Step 1 was left as one obligation,
`LoxodromicHypEmbeddedClosure`, stated at the hypothesis of
`FreeNormalSubgroupAtHypEmbedded`: the existence of a non-degenerate
hyperbolically embedded subgroup.

That is not the hypothesis the manuscript uses.  `DGOTheorem235Printed` is
stated at **acylindrical hyperbolicity**, and at that hypothesis step 1 is
already reachable, because the repository proves `(AH₁) ⇒ (AH₃)`:

* `GGT.exists_ah3Data_of_isAcylindricallyHyperbolic` builds an `AH3Data` — a
  loxodromic WPD element on a geodesic hyperbolic space — from
  `IsAcylindricallyHyperbolic`, on the geodesic realization of the Cayley
  graph;
* `GGT.dgoTheorem68_of` turns an `AH3Data` over a non-virtually-cyclic group
  into `E(elt) ↪_h G`, from the two named propositions
  `ElementaryConeOffHypEmbedded` and `ElementaryClosureProper` into which
  `GGT/WPDElementaryEmbedding` already cut Theorem 6.8;
* non-virtual-cyclicity is not an extra hypothesis: it follows from the
  non-elementary action inside `IsAcylindricallyHyperbolic`, by
  `HullSC.not_isVirtuallyCyclic_of_actsNonElementarily`.

So step 1 costs exactly the two propositions of Theorem 6.8, and this module
plumbs it: `exists_elementaryClosure_isHypEmbedded`.

## What the printed theorem then costs

`dgoTheorem235Printed_of_geometricInputs` assembles `DGOTheorem235Printed` from

* the three classical C⋆ citations of `DGOTheorem235Slice`
  (`PowersFreeGroupCStarSimple`, `AkemannLeeCStarSimplePermanence`,
  `BKKOUniqueTraceOfCStarSimple`);
* the two geometric propositions of Theorem 6.8; and
* `FreeNormalClosureOfPower`, their Theorem 7.19(e).

Steps 1 and 3 are gone: step 3 is proved in `GGT/HypEmbeddedCentralizer`, and
step 1 is the plumbing here.  What is left of the geometry is 6.8's cone-off
proposition and 7.19(e)'s free splitting — and `Osin's Theorem 5.4`, the
`(AH₄) ⇒ (AH₁)` direction, is **not** among them, because this route never
needs to go back from the hyperbolically embedded subgroup to acylindrical
hyperbolicity.

## Manuscript status

Infrastructure for `cor:regular-nonmf-algebra` through DGO 2.35; certifies no
printed sentence on its own.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreePrinted

open GroupApproximation.GGT
open GroupApproximation.GGT.Elementary
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

/-! ## Acylindrical hyperbolicity excludes virtual cyclicity -/

/-- **A non-elementary action forbids virtual cyclicity.**  The two independent
loxodromic elements inside `IsAcylindricallyHyperbolic` are exactly what
`HullSC.not_isVirtuallyCyclic_of_actsNonElementarily` consumes. -/
theorem not_isVirtuallyCyclic_of_isAcylindricallyHyperbolic (G : Type u)
    [Group G] [h : IsAcylindricallyHyperbolic G] : ¬ IsVirtuallyCyclic G := by
  obtain ⟨A, _, _, _, hne⟩ := h.out
  exact HullSC.not_isVirtuallyCyclic_of_actsNonElementarily
    (isIsometricAction_cayley A) hne

/-! ## Step 1 at the printed hypothesis -/

/-- **Step 1 of DGO's proof of Theorem 2.35, at acylindrical hyperbolicity.**

An acylindrically hyperbolic group contains an element of infinite order whose
elementary closure is hyperbolically embedded and proper.  The two hypotheses
are the propositions `GGT/WPDElementaryEmbedding` cuts their Theorem 6.8 into;
everything else is proved in the repository. -/
theorem exists_elementaryClosure_isHypEmbedded
    (hcone : ElementaryConeOffHypEmbedded.{u, u})
    (hproper : ElementaryClosureProper.{u, u})
    (G : Type u) [Group G] [IsAcylindricallyHyperbolic G] :
    ∃ c : G, IsHypEmbedded G (elementaryClosure c) ∧
      (∃ a : G, a ∉ elementaryClosure c) ∧ ∀ k : ℤ, k ≠ 0 → c ^ k ≠ 1 := by
  have hvc : ¬ IsVirtuallyCyclic G :=
    not_isVirtuallyCyclic_of_isAcylindricallyHyperbolic G
  obtain ⟨D⟩ := exists_ah3Data_of_isAcylindricallyHyperbolic G
  letI := D.metricSpace
  letI := D.mulAction
  obtain ⟨X, hX⟩ := hcone G D hvc
  refine ⟨D.elt,
    (HullSC.isHypEmbeddedOf_coneOff X (elementaryClosure D.elt) hX).isHypEmbedded,
    ?_, ?_⟩
  · have hne := hproper G D hvc
    by_contra hall
    push_neg at hall
    exact hne (Subgroup.eq_top_iff'.mpr hall)
  · intro k hk
    exact zpow_ne_one_of_isLoxodromic D.loxodromic hk

/-! ## The printed theorem from named inputs -/

/-- **Dahmani--Guirardel--Osin's Theorem 2.35, at its printed hypothesis, from
six named statements** — three classical C⋆ theorems, the two geometric
propositions of their Theorem 6.8, and their Theorem 7.19(e).

Steps 1 and 3 of their proof are discharged: step 3 in
`GGT/HypEmbeddedCentralizer`, step 1 above. -/
theorem dgoTheorem235Printed_of_geometricInputs
    (hPowers : PowersFreeGroupCStarSimple)
    (hAL : AkemannLeeCStarSimplePermanence)
    (hBKKO : BKKOUniqueTraceOfCStarSimple)
    (hcone : ElementaryConeOffHypEmbedded.{0, 0})
    (hproper : ElementaryClosureProper.{0, 0})
    (hsplit : FreeNormalClosureOfPower) : DGOTheorem235Printed := by
  intro G instG instC instAH hrad
  letI := instG
  letI := instC
  letI := instAH
  obtain ⟨c, hE, ⟨a, ha⟩, hinf⟩ :=
    exists_elementaryClosure_isHypEmbedded hcone hproper G
  obtain ⟨n, hn, hfree⟩ := hsplit G c hE hinf
  have hnz : ((n : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have hclosure : elementaryClosure (c ^ n) = elementaryClosure c := by
    rw [show c ^ n = c ^ ((n : ℕ) : ℤ) from (zpow_natCast c n).symm,
      elementaryClosure_zpow c hnz]
  have hcent : Subgroup.centralizer
      ((Subgroup.normalClosure ({c ^ n} : Set G) : Subgroup G) : Set G) = ⊥ := by
    refine centralizer_eq_bot_of_isHypEmbedded_elementaryClosure
      Subgroup.normalClosure_normal (c := c ^ n) (a := a)
        (Subgroup.subset_normalClosure rfl) ?_ ?_ hrad
    · rw [hclosure]
      exact hE
    · rw [hclosure]
      exact ha
  exact simpleUniqueTrace_of_free_normal_subgroup hPowers hAL hBKKO G
    (Subgroup.normalClosure ({c ^ n} : Set G)) Subgroup.normalClosure_normal
    hfree hcent

end TorsionFreePrinted
end NonMF
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted

#audit_axioms not_isVirtuallyCyclic_of_isAcylindricallyHyperbolic
#audit_axioms exists_elementaryClosure_isHypEmbedded
#audit_axioms dgoTheorem235Printed_of_geometricInputs
