import GroupApproximation.Manuscript.NonMF.FreeNormalSubgroupSlice
import GroupApproximation.GGT.OsinLemma512Torsion

/-!
# Step 1 of Dahmani--Guirardel--Osin's proof of Theorem 2.35, closed

`FreeNormalSubgroupSlice` opened the geometric residue of DGO's Theorem 2.35
along their steps 1 to 3, proved step 3, and left step 1 as one obligation:

> `LoxodromicHypEmbeddedClosure`: a countable group with a non-degenerate
> hyperbolically embedded subgroup and trivial finite radical contains an
> element `c` of infinite order whose elementary closure `E(c)` is
> hyperbolically embedded and proper.

This module proves it, with no hypothesis.  No new geometry is needed: every
ingredient is a theorem of the repository.

* `(AH₄) ⇒ (AH₁)`: Osin's Theorem 5.4 (`OsinEnlargement.osinTheorem54_unconditional`)
  and his Lemma 5.12 from Corollary 6.12 alone, torsion peripheral subgroups
  included (`OsinLemma512.relativeCayleyNonElementary_of_612` over
  `GGT.dgoCorollary612`), assembled by `GGT.osinAH4ToAH1_of`.
* `(AH₁) ⇒ (AH₃)` on the geodesic realization of the Cayley graph:
  `GGT.exists_ah3Data_of_isAcylindricallyHyperbolic`.
* DGO Corollary 2.9 at the witness, for the elementary closure itself rather
  than for an unnamed subgroup containing it: the finite transversal of
  Lemma 6.5 gives quasiconvexity and properness, the power-overlap form of
  Lemma 6.7 gives geometric separation, and DGO's Theorem 4.42
  (`Elementary.dgoTheorem442_unconditional`) turns the three into `E(c) ↪_h G`.
  The chain is the one inside `Elementary.dgoTheorem68_of_geodesic_projection`,
  kept here at the named subgroup because step 3 and step 2 consume `E(c)`.
* Properness of `E(c)`: `Elementary.elementaryClosureProper_unconditional`,
  from non-virtual-cyclicity, which the non-elementary clause of `(AH₁)` gives.

The two propositions into which `GGT/WPDElementaryEmbedding` had cut
Theorem 6.8, `ElementaryConeOffHypEmbedded` and `ElementaryClosureProper`, are
therefore not inputs of step 1 any more.

`freeNormalSubgroupAtHypEmbedded_of_freeNormalClosureOfPower` records the
consequence for the slice: the whole geometric residue of DGO 2.35 is now
their Theorem 7.19(e), `FreeNormalClosureOfPower`, and nothing else.

## Manuscript status

Infrastructure for `cor:regular-nonmf-algebra` (the sentence *"Dahmani,
Guirardel, and Osin give simplicity and uniqueness of the trace"*, tex line
1728); certifies no printed sentence on its own.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreePrinted

open GroupApproximation.HullGeometry
open GroupApproximation.GGT
open GroupApproximation.GGT.Elementary
open GroupApproximation.Manuscript.NonMF.TorsionFree

/-! ## Corollary 2.9 at the elementary closure -/

/-- **The elementary closure of the element of an `(AH₃)` witness is
hyperbolically embedded** (Dahmani--Guirardel--Osin, Corollary 2.9, for the
subgroup `E(elt)` itself).

The finite transversal of their Lemma 6.5 gives quasiconvexity of the orbit and
properness of the action, the power-overlap form of their Lemma 6.7 gives
geometric separation, and their Theorem 4.42 assembles the three. -/
theorem isHypEmbedded_elementaryClosure_of_ah3Data (G : Type) [Group G]
    (D : AH3Data.{0, 0} G) : IsHypEmbedded G (elementaryClosure D.elt) := by
  letI : PseudoMetricSpace D.Space := D.metricSpace
  letI : MulAction G D.Space := D.mulAction
  have hδ0 : 0 ≤ D.delta := nonneg_of_isHyperbolicSpace D.hyperbolic D.base
  have hclose :=
    elementaryClosureOrbitClose_of_geodesic D.hyperbolic hδ0 D.geodesic
      D.isometric D.loxodromic
  have hfin := elementaryClosureFiniteTransversalStatement_unconditional G D
  have hqc :=
    isQuasiconvexOrbitAt_elementaryClosure_of_finiteTransversal D.hyperbolic
      hδ0 D.isometric D.loxodromic hfin
  have hproper :=
    actsProperlyAt_elementaryClosure_of_finiteTransversal D.isometric
      D.loxodromic hfin
  have hsep :=
    geometricallySeparatedAt_elementaryClosure_of_diameterForcesConjugatePower
      (diameterForcesConjugatePowerAt_of_powerOrbit D.isometric hclose
        (dgoTheorem68PowerOverlap_unconditional G D))
  exact isHypEmbedded_of_dgo442 dgoTheorem442_unconditional
    (elementaryClosure D.elt) D.base D.delta D.isometric D.hyperbolic D.geodesic
    hqc hsep hproper

/-! ## Step 1 at acylindrical hyperbolicity -/

/-- **Step 1 of DGO's proof of Theorem 2.35, at acylindrical hyperbolicity,
unconditional.**  An acylindrically hyperbolic group contains an element of
infinite order whose elementary closure is hyperbolically embedded and proper. -/
theorem exists_elementaryClosure_isHypEmbedded_of_isAcylindricallyHyperbolic
    (G : Type) [Group G] [hG : IsAcylindricallyHyperbolic G] :
    ∃ c : G, IsHypEmbedded G (elementaryClosure c) ∧
      (∃ a : G, a ∉ elementaryClosure c) ∧ ∀ k : ℤ, k ≠ 0 → c ^ k ≠ 1 := by
  obtain ⟨D⟩ := exists_ah3Data_of_isAcylindricallyHyperbolic G
  obtain ⟨A, _δ, _hδ, _hacy, hne⟩ := hG.out
  have hnvc : ¬ IsVirtuallyCyclic G :=
    HullSC.not_isVirtuallyCyclic_of_actsNonElementarily
      (isIsometricAction_cayley A) hne
  have hproper : elementaryClosure D.elt ≠ ⊤ :=
    elementaryClosureProper_unconditional G D hnvc
  refine ⟨D.elt, isHypEmbedded_elementaryClosure_of_ah3Data G D, ?_, ?_⟩
  · by_contra hall
    refine hproper (Subgroup.eq_top_iff'.mpr fun x => ?_)
    by_contra hx
    exact hall ⟨x, hx⟩
  · intro k hk
    letI : PseudoMetricSpace D.Space := D.metricSpace
    letI : MulAction G D.Space := D.mulAction
    exact zpow_ne_one_of_isLoxodromic D.loxodromic hk

/-! ## Step 1 at the hypothesis of the slice -/

/-- **A non-degenerate hyperbolically embedded subgroup makes a group
acylindrically hyperbolic** (Osin, Theorem 1.2, `(AH₄) ⇒ (AH₁)`), from his
Theorem 5.4 and his Lemma 5.12, both proved; the peripheral subgroup may be
torsion. -/
theorem isAcylindricallyHyperbolic_of_isNonDegenerate_isHypEmbedded
    {G : Type} [Group G] {E : Subgroup G} (hE : IsNonDegenerate E)
    (hemb : IsHypEmbedded G E) : IsAcylindricallyHyperbolic G :=
  osinAH4ToAH1_of OsinEnlargement.osinTheorem54_unconditional
    (OsinLemma512.relativeCayleyNonElementary_of_612 dgoCorollary612)
    G E hE.1 hE.2 hemb

/-- **`LoxodromicHypEmbeddedClosure`, proved.**  Dahmani--Guirardel--Osin's
Theorem 6.14(c) at `n = 1` together with their Theorem 6.8, in the form step 2
and step 3 of their proof of Theorem 2.35 consume. -/
theorem loxodromicHypEmbeddedClosure : LoxodromicHypEmbeddedClosure := by
  intro G _instG _instC hemb _hrad
  obtain ⟨E, hE, hEmb⟩ := hemb
  haveI : IsAcylindricallyHyperbolic G :=
    isAcylindricallyHyperbolic_of_isNonDegenerate_isHypEmbedded hE hEmb
  exact exists_elementaryClosure_isHypEmbedded_of_isAcylindricallyHyperbolic G

/-- **The geometric residue of DGO 2.35 is their Theorem 7.19(e) alone.**
Step 1 is `loxodromicHypEmbeddedClosure`, step 3 is
`GGT.centralizer_eq_bot_of_isHypEmbedded_elementaryClosure`. -/
theorem freeNormalSubgroupAtHypEmbedded_of_freeNormalClosureOfPower
    (h2 : FreeNormalClosureOfPower) : FreeNormalSubgroupAtHypEmbedded :=
  freeNormalSubgroupAtHypEmbedded_of_inputs loxodromicHypEmbeddedClosure h2

end TorsionFreePrinted
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrinted.isHypEmbedded_elementaryClosure_of_ah3Data
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrinted.exists_elementaryClosure_isHypEmbedded_of_isAcylindricallyHyperbolic
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrinted.isAcylindricallyHyperbolic_of_isNonDegenerate_isHypEmbedded
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrinted.loxodromicHypEmbeddedClosure
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrinted.freeNormalSubgroupAtHypEmbedded_of_freeNormalClosureOfPower
