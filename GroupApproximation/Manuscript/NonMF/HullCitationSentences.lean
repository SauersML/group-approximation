import GroupApproximation.GGT.OsinLimitSetSpelling
import GroupApproximation.GGT.HullSC
import GroupApproximation.GGT.HullTheorem316Assembly
import GroupApproximation.GGT.HullSCLemma44BoundedLeastAreaCanonical
import GroupApproximation.GGT.HullSCCommonQuotientPrinted
import GroupApproximation.Manuscript.NonMF.HullPrintedInputs
import GroupApproximation.Meta.AxiomGuard

/-!
# Hull's cited results in `sec:torsion-free`, other than Theorem 7.1

`non_mf_groups_exist.tex` cites M. Hull, *Small cancellation in acylindrically
hyperbolic groups*, at five places other than Theorem 7.1 itself:

* Theorem 3.12, for the generating set `A` (tex line 1630);
* Definition 1.4, *suitable* (tex line 1632), which is the definition
  `TorsionFree.Suitable`, with clause 1 of Hull's definition carried by
  `TorsionFree.HullGeneratingSet`;
* the proof of Theorem 7.1, for the induction on `m` (tex line 1646), which is the
  one-step form of Theorem 7.1 and rests on its leaves;
* Corollary 5.7 with Lemma 5.8, for the pair `h₁, h₂` in the proof of
  `lem:saturation` (tex line 1662);
* Corollary 7.4, for the common quotient `G₀` in the Fournier-Facio paragraph
  (tex line 1682).

This module proves Theorem 3.12 (1) ⇔ (4) at the manuscript's notion of acylindrical
hyperbolicity, Corollary 5.7 as printed, and the sentence of `lem:saturation` that
applies Corollary 5.7 with Lemma 5.8, all without hypotheses.  Corollary 7.4 in the
form the manuscript uses comes from Theorem 7.1, so its carrier takes the two
least-area leaves of Theorem 7.1.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace HullCitationSentences

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted

/-! ## Hull, Theorem 3.12 -/

/-- **"For an acylindrically hyperbolic group `G`, choose the generating set `A`
provided by Hull [Theorem 3.12]."** (tex lines 1629–1630, `sec:torsion-free`).

Acylindrically hyperbolic is Osin's notion, as the manuscript uses it: an acylindrical
isometric action on a geodesic hyperbolic space that is non-elementary
(`GGT.SequentialBoundary.IsAcylindricallyHyperbolicLimitSet`).  The generating set is
Hull's Theorem 3.12(4): `Γ(G,A)` is hyperbolic and the action of `G` on it is
acylindrical and non-elementary (`TorsionFree.HullGeneratingSet`). -/
def PrintedHullGeneratingSetLimitSet : Prop :=
  ∀ (G : Type) [Group G], GGT.SequentialBoundary.IsAcylindricallyHyperbolicLimitSet G →
    Nonempty (HullGeneratingSet G)

/-- The sentence at tex line 1630, proved: the hard direction of Osin's Theorem 1.1
(`GGT.OsinClassification.isAcylindricallyHyperbolicOsin_of_limitSet`), then Osin's
notion to Hull's Cayley-graph notion (`GGT.exists_hullGeneratingSet_of_osin`). -/
theorem printedHullGeneratingSetLimitSet : PrintedHullGeneratingSetLimitSet := by
  intro G _ hG
  exact GGT.exists_hullGeneratingSet_of_osin G
    (GGT.OsinClassification.isAcylindricallyHyperbolicOsin_of_limitSet G hG)

/-- **Hull, Theorem 3.12, (1) ⇔ (4)**, at the manuscript's notion: a group is
acylindrically hyperbolic exactly when it has a generating set `A` with `Γ(G,A)`
hyperbolic and the action of `G` on `Γ(G,A)` non-elementary and acylindrical. -/
def PrintedHullTheorem312LimitSet : Prop :=
  ∀ (G : Type) [Group G],
    GGT.SequentialBoundary.IsAcylindricallyHyperbolicLimitSet G ↔
      Nonempty (HullGeneratingSet G)

/-- Hull's Theorem 3.12, (1) ⇔ (4), proved.  The converse is
`HullSC.isAcylindricallyHyperbolic_of_hullGeneratingSet` with the easy direction of
Osin's Theorem 1.1. -/
theorem printedHullTheorem312LimitSet : PrintedHullTheorem312LimitSet := by
  intro G _
  refine ⟨printedHullGeneratingSetLimitSet G, ?_⟩
  rintro ⟨A⟩
  exact @GGT.SequentialBoundary.isAcylindricallyHyperbolicLimitSet_of_isAcylindricallyHyperbolic
    G _ (HullSC.isAcylindricallyHyperbolic_of_hullGeneratingSet A)

/-- **Hull, Theorem 3.12, (1) ⇔ (4)**, at Osin's Definition 1.3 spelling
`GGT.IsAcylindricallyHyperbolicOsin` (non-elementary as two independent
loxodromic elements). -/
def PrintedHullTheorem312Osin : Prop :=
  ∀ (G : Type) [Group G],
    GGT.IsAcylindricallyHyperbolicOsin G ↔ Nonempty (HullGeneratingSet G)

/-- Hull's Theorem 3.12, (1) ⇔ (4), at Osin's spelling, proved. -/
theorem printedHullTheorem312Osin : PrintedHullTheorem312Osin := by
  intro G _
  refine ⟨GGT.exists_hullGeneratingSet_of_osin G, ?_⟩
  rintro ⟨A⟩
  exact @GGT.osin_of_isAcylindricallyHyperbolic G _
    (HullSC.isAcylindricallyHyperbolic_of_hullGeneratingSet A)

/-! ## Hull, Corollary 5.7 and Lemma 5.8 -/

/-- **Hull, Corollary 5.7**, as printed: *"Suppose `S` is suitable with respect to
`A`.  Then for all `k ∈ ℕ`, `S` contains non-commensurable, loxodromic elements
`h₁,…,h_k` such that `E_G(hᵢ) = ⟨hᵢ⟩` … In particular,
`{⟨h₁⟩,…,⟨h_k⟩} ↪h (G, A)`."*

`E_G(h)` is `GGT.Elementary.elementaryClosure h`, and the hyperbolically embedded
family is the cone-off of `Γ(G,A)` along the cyclic subgroups.  The last clause is
stated for `k > 0`, where the family is nonempty. -/
def PrintedHullCorollary57 : Prop :=
  ∀ {G : Type} [Group G] (A : HullGeneratingSet G) {S : Subgroup G},
    Suitable A.alphabet S → ∀ k : ℕ,
      ∃ h : Fin k → G, (∀ i, h i ∈ S) ∧
        (∀ i, IsLoxodromic (h i) (Cayley.base A.alphabet)) ∧
          HullSC.PairwiseNonCommensurable h ∧
            (∀ i, GGT.Elementary.elementaryClosure (h i) = Subgroup.zpowers (h i)) ∧
              (0 < k → (HullSC.coneOffFamily A.alphabet
                (fun i => Subgroup.zpowers (h i))).IsHyperbolicallyEmbedded)

/-- Hull's Corollary 5.7, proved: the elements are `HullSC.yiSuitableFiniteFamily_closed`,
and the cyclic family they generate is hyperbolically embedded by
`HullSC.isHyperbolicallyEmbedded_zpowers_of_elementaryClosure_eq_unconditional`. -/
theorem printedHullCorollary57 : PrintedHullCorollary57 := by
  intro G _ A S hS k
  obtain ⟨h, hmem, hlox, hncom, hcyc⟩ := HullSC.yiSuitableFiniteFamily_closed A hS k
  refine ⟨h, hmem, hlox, hncom, hcyc, fun hk => ?_⟩
  haveI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  exact HullSC.isHyperbolicallyEmbedded_zpowers_of_elementaryClosure_eq_unconditional
    A h hncom hlox hcyc

/-- **"By Hull [Corollary 5.7 and Lemma 5.8], `N` contains two elements `h₁,h₂`
such that `N₀ = ⟨h₁,h₂⟩` is suitable with respect to a generating set `A' ⊇ A` to
which Hull's small cancellation theorem again applies."** (tex line 1662, proof of
`lem:saturation`).

`G` is torsion-free there.  *To which Hull's small cancellation theorem again applies*
is that `A'` is again a Hull generating set, so `thm:hull` takes `N₀` and `A'` as its
data; the application itself is the next sentence. -/
def PrintedSaturationHullPair : Prop :=
  ∀ {G : Type} [Group G], IsPowerTorsionFree G →
    ∀ (A : HullGeneratingSet G) {N : Subgroup G}, Suitable A.alphabet N →
      ∃ A' : HullGeneratingSet G, A.alphabet.carrier ⊆ A'.alphabet.carrier ∧
        ∃ h₁ ∈ N, ∃ h₂ ∈ N,
          Suitable A'.alphabet (Subgroup.closure ({h₁, h₂} : Set G))

/-- The sentence at tex line 1662, proved with `A' = A`
(`TorsionFreePrinted.hullSuitablePair_of_torsionFree`).  Two independent loxodromic
elements of `N` already generate a non-elementary subgroup, and over a torsion-free
group the finite-normalizer clause of Hull's Definition 1.4 is automatic, so
Lemma 5.8 is not needed in this case. -/
theorem printedSaturationHullPair : PrintedSaturationHullPair := by
  intro G _ hG A N hN
  exact hullSuitablePair_of_torsionFree hG A hN

/-! ## Hull, Corollary 7.4 -/

/-- **"The group `G₀` is obtained there as a common quotient of two finitely
generated acylindrically hyperbolic groups by Hull's theorem [Corollary 7.4], which
allows the quotient to be chosen acylindrically hyperbolic; we take `G₀` to be such a
quotient."** (tex lines 1681–1684, the Fournier-Facio paragraph).

`TorsionFreePrinted.HullCommonQuotientPrinted` is Corollary 7.4 at the groups the
paragraph applies it to: `G₁, G₂` finitely presented, torsion-free and acylindrically
hyperbolic with trivial finite radical (Hull's `K(Gᵢ) = {1}`), and a finite `Ω ⊆ G₁`
on which `α₁` is injective.  The common quotient is finitely presented, torsion-free
and acylindrically hyperbolic.  Hull derives Corollary 7.4 from Theorem 7.1, so the
carrier takes the two least-area leaves of Theorem 7.1
(`HullSC.hullOneStepStatement_of_leastAreaLeaves`) and passes through the one-step
quotients (`HullSC.hullCommonQuotientPrinted_of_oneStep`). -/
theorem manuscriptSentence_hullCommonQuotient_of_leastAreaLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    HullCommonQuotientPrinted :=
  HullSC.hullCommonQuotientPrinted_of_oneStep
    (HullSC.hullOneStepStatement_of_leastAreaLeaves hgreendlinger hbridge)

end HullCitationSentences
end NonMF
end Manuscript
end GroupApproximation

#audit_closed_axioms GroupApproximation.Manuscript.NonMF.HullCitationSentences.printedHullGeneratingSetLimitSet
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.HullCitationSentences.printedHullTheorem312LimitSet
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.HullCitationSentences.printedHullTheorem312Osin
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.HullCitationSentences.printedHullCorollary57
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.HullCitationSentences.printedSaturationHullPair
#audit_axioms GroupApproximation.Manuscript.NonMF.HullCitationSentences.manuscriptSentence_hullCommonQuotient_of_leastAreaLeaves
