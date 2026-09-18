import GroupApproximation.Manuscript.NonMF.Saturation.PrintedRouteGreendlinger
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:saturation` along the printed route (`A' ⊇ A`), over the least-area Greendlinger leaf

Lane gl-assembly-06.  `non_mf_groups_exist.tex`, lines 2136–2156:

> **Lemma (saturation).** Let `G` be finitely presented, torsion-free, and acylindrically
> hyperbolic, and let `N ⊴ G` be nontrivial. …
>
> *Proof.* … By Hull [Corollary 5.7 and Lemma 5.8], `N` contains two elements `h₁,h₂` such that
> `N₀ = ⟨h₁,h₂⟩` is suitable with respect to a generating set `A' ⊇ A` to which Hull's small
> cancellation theorem again applies.  Apply Theorem `thm:hull` to `N₀`, with respect to `A'`,
> with `g₁,…,g_m` a finite generating set of `G`. …

## Route

`Saturation.manuscriptSentence_saturationApplyHullPrintedRoute_of_greendlinger` and
`Saturation.manuscriptSentence_saturationPrintedRoute_of_greendlinger`
(`Saturation/PrintedRouteGreendlinger`) take the leaf as the binder `hgreendlinger`.  The lane's
closed endpoints would apply them to
`GGT.VanKampen.GreendlingerLeaf.AsmClose.relativeGreendlingerQuasiGeodesicLeastAreaClosed.{0,0,0}`
(lane gl-assembly-04), which is not yet on disk.  So the interface is the existing Statement
`GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}` (Osin's Lemma 4.4 at
least-area diagrams, TRUE), and both endpoints keep the printed binders `G, hG, A, hN`.

## Manuscript status

Partial on `hgreendlinger` only.  Everything else on this route is closed: Osin's Lemma 7.1, Hull's
Corollary 5.7 and Lemma 5.8, the embedded bridge, and the group theory after `thm:hull`.
-/

namespace GroupApproximation.Manuscript.NonMF.GreendlingerClosedSaturation

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

/-- **"Apply Theorem `thm:hull` to `N₀`, with respect to `A'`, with `g₁,…,g_m` a finite generating
set of `G`."** (tex line 2144), with the printed binders `G, hG, A, hN`, over the least-area
Greendlinger leaf. -/
theorem manuscriptSentence_saturationApplyHullPrintedRoute_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    {G : Type} [Group G] [Group.IsFinitelyPresented G] [IsAcylindricallyHyperbolic G]
    (hG : IsPowerTorsionFree G) (A : HullGeneratingSet G) {N : Subgroup G}
    (hN : Suitable A.alphabet N) :
    ∃ A' : HullGeneratingSet G, A.alphabet.carrier ⊆ A'.alphabet.carrier ∧
      ∃ h₁ ∈ N, ∃ h₂ ∈ N, Subgroup.closure ({h₁, h₂} : Set G) ≤ N ∧
        Suitable A'.alphabet (Subgroup.closure ({h₁, h₂} : Set G)) ∧
          ∃ (m : ℕ) (t : Fin m → G), Subgroup.closure (Set.range t) = ⊤ ∧
            Nonempty (HullCorrectedInputs.HullQuotientNG
              (Subgroup.closure ({h₁, h₂} : Set G)) t (∅ : Set G)) :=
  Saturation.manuscriptSentence_saturationApplyHullPrintedRoute_of_greendlinger hgreendlinger hG
    A hN

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedSaturation.manuscriptSentence_saturationApplyHullPrintedRoute_of_greendlinger

/-- **`lem:saturation`** (tex lines 2136–2141) along the printed proof, with the pair taken at
`A' ⊇ A`, over the least-area Greendlinger leaf. -/
theorem manuscriptSentence_saturationPrintedRoute_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreePrinted.PrintedSaturationNoOmega.{0} :=
  Saturation.manuscriptSentence_saturationPrintedRoute_of_greendlinger hgreendlinger

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedSaturation.manuscriptSentence_saturationPrintedRoute_of_greendlinger

end GroupApproximation.Manuscript.NonMF.GreendlingerClosedSaturation
