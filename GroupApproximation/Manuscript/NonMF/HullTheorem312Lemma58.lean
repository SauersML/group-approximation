import Mathlib.Tactic.TFAE
import GroupApproximation.GGT.OsinLimitSetSpelling
import GroupApproximation.GGT.AcylindricallyHyperbolicLimitSetEasy
import GroupApproximation.GGT.AcylindricallyHyperbolicOsin
import GroupApproximation.GGT.AH3GeodesicCayley
import GroupApproximation.GGT.DGOTheorem442Proof
import GroupApproximation.GGT.HullSC
import GroupApproximation.GGT.OsinLemma512Torsion
import GroupApproximation.GGT.DGOCorollary612Unconditional
import GroupApproximation.GGT.OsinTheorem54Unconditional
import GroupApproximation.GGT.DGOCorollary427PairLocal
import GroupApproximation.GGT.DGOProposition433Finite
import GroupApproximation.GGT.OsinTheorem54SepElementaryBall
import GroupApproximation.GGT.ElementaryOsinSNormal
import GroupApproximation.GGT.ElementaryMorseAlphabet
import GroupApproximation.Manuscript.NonMF.OsinTheorem12NonDegenerate
import GroupApproximation.Meta.AxiomGuard

/-!
# Hull, Theorem 3.12 and Lemma 5.8, as printed

M. Hull, *Small cancellation in acylindrically hyperbolic groups*, arXiv:1308.4345.
`non_mf_groups_exist.tex` cites Theorem 3.12 for the generating set `A` (tex line 1629) and
Lemma 5.8 with Corollary 5.7 in the proof of `lem:saturation` (tex line 1659).
`Manuscript.NonMF.HullCitationSentences` proves (1) ⇔ (4) of Theorem 3.12 and Corollary 5.7.
This module proves the whole of Theorem 3.12 and Lemma 5.8, at the generality Hull prints.

> **Theorem 3.12.** The following are equivalent:
> 1. `G ∈ AH`.
> 2. `G` is not virtually cyclic and `G` admits an action on a hyperbolic metric space such
>    that `G` contains at least one loxodromic, WPD element.
> 3. `G` contains a non-degenerate hyperbolically embedded subgroup.
> 4. For some generating set `A ⊆ G`, `Γ(G,A)` is hyperbolic and the action of `G` on
>    `Γ(G,A)` is non-elementary and acylindrical.

> **Lemma 5.8.** If `S` contains an infinite order element `h` such that `⟨h⟩` is a proper
> subgroup of `S` and `⟨h⟩ ↪h (G,X)`, then `S` is suitable with respect to `A` for some
> `A ⊇ X`.

## Conventions

* `G ∈ AH` (Hull, Definition 1.3) is `GGT.SequentialBoundary.IsAcylindricallyHyperbolicLimitSet`:
  an acylindrical isometric action on a geodesic hyperbolic space whose limit set has more
  than two points.  Hull's hyperbolic spaces are geodesic (§2: "A geodesic metric space `X`
  is called `δ`-hyperbolic if …").
* Clause (2) is `GGT.AH3Data`: an isometric action on a geodesic hyperbolic space with a
  loxodromic WPD element.
* In clause (3), non-degenerate means proper and infinite (`GGT.IsNonDegenerate`), and
  `H ↪h G` is `GGT.IsHypEmbedded`.
* Clause (4) is `TorsionFree.HullGeneratingSet`.  Its alphabet is symmetric, and `Γ(G,A)`
  and `Γ(G, A ∪ A⁻¹)` are the same graph.
* *Suitable with respect to `A`* (Hull, Definition 1.4) has three clauses.  Clause (1),
  `Γ(G,A)` hyperbolic with acylindrical action, is carried by `HullGeneratingSet`, whose
  remaining field (`G` acts non-elementarily) follows from clause (2).  Clauses (2) and (3),
  `S` acts non-elementarily and normalizes no nontrivial finite subgroup, are
  `TorsionFree.Suitable A S`.
* `⟨h⟩ ↪h (G,X)` is `GGT.IsHypEmbeddedOf G X (zpowers h)`, which also asks that `X ∪ ⟨h⟩`
  be symmetric.  Replacing `X` by `X ∪ X⁻¹` changes neither `Γ(G, X ⊔ ⟨h⟩)` nor the relative
  metric on `⟨h⟩`, and `A ⊇ X ∪ X⁻¹` implies `A ⊇ X`.

## The proofs

Theorem 3.12 assembles proved theorems.  (1) ⇒ (4) is Osin's Theorem 1.1
(`OsinClassification.isAcylindricallyHyperbolicOsin_of_limitSet`), and (4) ⇒ (1) its easy
direction.  (4) ⇒ (2) uses the geodesic realization of the Cayley graph, and (2) ⇒ (4) is
Osin's Theorem 1.2 (`Elementary.osinTheorem12_unconditional`).  (4) ⇒ (3) is
`TorsionFreePrinted.exists_isNonDegenerate_isHypEmbedded`, and (3) ⇒ (4) is Osin's
Theorem 5.4 with his Lemma 5.12.

Lemma 5.8 follows Hull's proof.  Take `g ∈ S \ ⟨h⟩` and adjoin `g^{±1}` to `X`
(Dahmani--Guirardel--Osin, Corollary 4.27: `RelGenSet.pairLocalFiniteness`).  Osin's
Theorem 5.4 then enlarges the base to `Y`, and `G` acts acylindrically on `Γ(G, Y ⊔ ⟨h⟩)`;
this is the alphabet `A`.  Dahmani--Guirardel--Osin's Corollary 6.12 gives `k ∈ ⟨h⟩` with
`gk` loxodromic.  The element `h` is elliptic of infinite order, so it lies outside the
elementary closure of `gk`, and `S` acts non-elementarily.  A finite subgroup normalized by
`S` lies in `⟨h⟩` (`normalizesNoNontrivialFinite_of_isHyperbolicallyEmbedded`), and an
infinite cyclic group has no nontrivial finite subgroup.

Hull obtains the loxodromic from his Lemma 3.9 for any `g ∈ S \ ⟨h⟩`.  The repository's
Corollary 6.12 takes the letter `g` in the base, which is why `g^{±1}` is adjoined first.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace HullTheorem312Lemma58

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

/-! ## Hull, Theorem 3.12 -/

/-- **Hull, Theorem 3.12**, as printed: for a group `G` the following are equivalent.
(1) `G ∈ AH`.  (2) `G` is not virtually cyclic and acts on a hyperbolic space with a
loxodromic WPD element.  (3) `G` contains a non-degenerate hyperbolically embedded subgroup.
(4) For some generating set `A`, `Γ(G,A)` is hyperbolic and the action of `G` on it is
non-elementary and acylindrical. -/
def PrintedHullTheorem312 : Prop :=
  ∀ (G : Type) [Group G],
    [GGT.SequentialBoundary.IsAcylindricallyHyperbolicLimitSet G,
      ¬ GGT.IsVirtuallyCyclic G ∧ Nonempty (GGT.AH3Data.{0, 0} G),
      (∃ E : Subgroup G, GGT.IsNonDegenerate E ∧ GGT.IsHypEmbedded G E),
      Nonempty (HullGeneratingSet G)].TFAE

/-- Hull's Theorem 3.12, proved.  Every implication goes through (4). -/
theorem printedHullTheorem312 : PrintedHullTheorem312 := by
  intro G _
  have h14 : GGT.SequentialBoundary.IsAcylindricallyHyperbolicLimitSet G →
      Nonempty (HullGeneratingSet G) := fun hG =>
    GGT.exists_hullGeneratingSet_of_osin G
      (GGT.OsinClassification.isAcylindricallyHyperbolicOsin_of_limitSet G hG)
  have h41 : Nonempty (HullGeneratingSet G) →
      GGT.SequentialBoundary.IsAcylindricallyHyperbolicLimitSet G := by
    rintro ⟨A⟩
    exact @GGT.SequentialBoundary.isAcylindricallyHyperbolicLimitSet_of_isAcylindricallyHyperbolic
      G _ (HullSC.isAcylindricallyHyperbolic_of_hullGeneratingSet A)
  have h42 : Nonempty (HullGeneratingSet G) →
      ¬ GGT.IsVirtuallyCyclic G ∧ Nonempty (GGT.AH3Data.{0, 0} G) := by
    rintro ⟨A⟩
    exact ⟨HullSC.not_isVirtuallyCyclic_of_actsNonElementarily
        (isIsometricAction_cayley A.alphabet) A.nonElementary,
      @GGT.exists_ah3Data_of_isAcylindricallyHyperbolic G _
        (HullSC.isAcylindricallyHyperbolic_of_hullGeneratingSet A)⟩
  have h24 : ¬ GGT.IsVirtuallyCyclic G ∧ Nonempty (GGT.AH3Data.{0, 0} G) →
      Nonempty (HullGeneratingSet G) := by
    rintro ⟨hnvc, ⟨D⟩⟩
    exact @exists_hullGeneratingSet G _
      (GGT.Elementary.osinTheorem12_unconditional G D hnvc)
  have h43 : Nonempty (HullGeneratingSet G) →
      ∃ E : Subgroup G, GGT.IsNonDegenerate E ∧ GGT.IsHypEmbedded G E := by
    rintro ⟨A⟩
    exact @TorsionFreePrinted.exists_isNonDegenerate_isHypEmbedded G _
      (HullSC.isAcylindricallyHyperbolic_of_hullGeneratingSet A)
  have h34 : (∃ E : Subgroup G, GGT.IsNonDegenerate E ∧ GGT.IsHypEmbedded G E) →
      Nonempty (HullGeneratingSet G) := by
    rintro ⟨E, ⟨hne, hinf⟩, hemb⟩
    exact @exists_hullGeneratingSet G _
      (GGT.osinAH4ToAH1_of GGT.OsinEnlargement.osinTheorem54_unconditional
        (GGT.OsinLemma512.relativeCayleyNonElementary_of_612 GGT.dgoCorollary612)
        G E hne hinf hemb)
  tfae_have 1 → 4 := h14
  tfae_have 4 → 1 := h41
  tfae_have 4 → 2 := h42
  tfae_have 2 → 4 := h24
  tfae_have 4 → 3 := h43
  tfae_have 3 → 4 := h34
  tfae_finish

#audit_closed_axioms printedHullTheorem312

/-! ## Hull, Lemma 5.8 -/

/-- **The finite-normalizer clause of Hull's Lemma 5.8.**  If the infinite cyclic group
`⟨h⟩` is hyperbolically embedded with respect to `D` and `h ∈ S`, then `S` normalizes no
nontrivial finite subgroup.

Let `f` lie in a finite subgroup `F` normalized by `S`.  The conjugates `hⁿ f h⁻ⁿ` take
finitely many values, so a nonzero power `hᴺ` commutes with `f`.  Every `hᴺᵏ` then lies in
`⟨h⟩ ∩ f⟨h⟩f⁻¹`, which is therefore infinite, and Dahmani--Guirardel--Osin's
Proposition 4.33(b) (`GGT.finite_conj_inter_of_notMem`) forces `f ∈ ⟨h⟩`.  An element of
`⟨h⟩` of finite order is `1`. -/
theorem normalizesNoNontrivialFinite_of_isHyperbolicallyEmbedded {G : Type u} [Group G]
    (D : GGT.RelGenSet G Unit) (hemb : D.IsHyperbolicallyEmbedded) {h : G}
    (hfam : D.fam () = Subgroup.zpowers h) (hord : ¬ IsOfFinOrder h) {S : Subgroup G}
    (hS : h ∈ S) : HullSuitable.NormalizesNoNontrivialFinite S := by
  intro F hF hnorm
  have hinj : Function.Injective (fun n : ℤ => h ^ n) :=
    injective_zpow_iff_not_isOfFinOrder.mpr hord
  rw [Subgroup.eq_bot_iff_forall]
  intro f hf
  -- a nonzero power of `h` commutes with `f`
  obtain ⟨m, n, hmn, hmneq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun j : ℤ => (⟨h ^ j * f * (h ^ j)⁻¹, hnorm (h ^ j) (zpow_mem hS j) f hf⟩ : F))
  have e : h ^ m * f * (h ^ m)⁻¹ = h ^ n * f * (h ^ n)⁻¹ := congrArg Subtype.val hmneq
  have hc : Commute (h ^ (-n + m)) f := by
    change h ^ (-n + m) * f = f * h ^ (-n + m)
    rw [zpow_add, zpow_neg]
    calc (h ^ n)⁻¹ * h ^ m * f
        = (h ^ n)⁻¹ * (h ^ m * f * (h ^ m)⁻¹) * h ^ m := by
          simp only [mul_assoc, inv_mul_cancel, mul_one]
      _ = (h ^ n)⁻¹ * (h ^ n * f * (h ^ n)⁻¹) * h ^ m := by rw [e]
      _ = f * ((h ^ n)⁻¹ * h ^ m) := by simp only [mul_assoc, inv_mul_cancel_left]
  have hN0 : -n + m ≠ 0 := fun h0 => hmn (by omega)
  -- so `f ∈ ⟨h⟩`
  have hfH : f ∈ Subgroup.zpowers h := by
    by_contra hfH
    have hfin : {x : G | x ∈ D.fam () ∧ f⁻¹ * x * f ∈ D.fam ()}.Finite :=
      GGT.finite_conj_inter_of_notMem D hemb (by rw [hfam]; exact hfH)
    have hψ : Function.Injective (fun k : ℤ => h ^ ((-n + m) * k)) :=
      hinj.comp (mul_right_injective₀ hN0)
    have hsub : Set.range (fun k : ℤ => h ^ ((-n + m) * k)) ⊆
        {x : G | x ∈ D.fam () ∧ f⁻¹ * x * f ∈ D.fam ()} := by
      rintro _ ⟨k, rfl⟩
      have hx : h ^ ((-n + m) * k) ∈ D.fam () := by
        rw [hfam]
        exact Subgroup.zpow_mem_zpowers h _
      have hck : Commute (h ^ ((-n + m) * k)) f := by
        rw [zpow_mul]
        exact hc.zpow_left k
      have hconj : f⁻¹ * h ^ ((-n + m) * k) * f = h ^ ((-n + m) * k) := by
        rw [mul_assoc, hck.eq, inv_mul_cancel_left]
      show h ^ ((-n + m) * k) ∈ {x : G | x ∈ D.fam () ∧ f⁻¹ * x * f ∈ D.fam ()}
      exact ⟨hx, by rw [hconj]; exact hx⟩
    exact Set.Infinite.mono hsub (Set.infinite_range_of_injective hψ) hfin
  -- torsion in `⟨h⟩` is trivial
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hfH
  obtain ⟨i, j, hij, hijeq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun j : ℤ => (⟨(h ^ k) ^ j, zpow_mem hf j⟩ : F))
  have e' : h ^ (k * i) = h ^ (k * j) := by
    rw [zpow_mul, zpow_mul]
    exact congrArg Subtype.val hijeq
  rcases mul_eq_mul_left_iff.mp (hinj e') with hij' | hk0
  · exact absurd hij' hij
  · rw [hk0, zpow_zero]

#audit_axioms normalizesNoNontrivialFinite_of_isHyperbolicallyEmbedded

/-- **Hull, Lemma 5.8**, as printed: *"If `S` contains an infinite order element `h` such
that `⟨h⟩` is a proper subgroup of `S` and `⟨h⟩ ↪h (G,X)`, then `S` is suitable with
respect to `A` for some `A ⊇ X`."*

*Suitable with respect to `A`* is a Hull generating set `A` (clause (1) of Hull's
Definition 1.4) with `TorsionFree.Suitable A S` (clauses (2) and (3)). -/
def PrintedHullLemma58 : Prop :=
  ∀ {G : Type u} [Group G] (X : Set G) (S : Subgroup G) (h : G), h ∈ S →
    ¬ IsOfFinOrder h → Subgroup.zpowers h < S →
      GGT.IsHypEmbeddedOf G X (Subgroup.zpowers h) →
        ∃ A : HullGeneratingSet G, X ⊆ A.alphabet.carrier ∧ Suitable A.alphabet S

/-- Hull's Lemma 5.8, proved along Hull's proof; see the module docstring. -/
theorem printedHullLemma58 : PrintedHullLemma58.{u} := by
  intro G _ X S h hS hord hlt hX
  obtain ⟨D, hbase, hfam, hemb⟩ := hX
  have hDfam : D.fam () = Subgroup.zpowers h := congrFun hfam ()
  -- `g ∈ S \ ⟨h⟩`, adjoined to the base
  obtain ⟨g, hgS, hgH⟩ := SetLike.exists_of_lt hlt
  have hemb₁ : (D.adjoinPair g).IsHyperbolicallyEmbedded :=
    GGT.RelGenSet.isHyperbolicallyEmbedded_adjoinPair_of_localFiniteness
      GGT.RelGenSet.pairLocalFiniteness D hemb g
  -- Osin's Theorem 5.4: the alphabet `A = Y ⊔ ⟨h⟩`
  obtain ⟨D', hbase', hfam', hemb', hacy⟩ :=
    GGT.OsinEnlargement.osinTheorem54_unconditional G (D.adjoinPair g) hemb₁
  obtain ⟨δ, hδ⟩ := hemb'.hyperbolic
  have hD'fam : D'.fam () = Subgroup.zpowers h := by
    rw [hfam']
    exact hDfam
  -- Dahmani--Guirardel--Osin's Corollary 6.12: `gk` is loxodromic for some `k ∈ ⟨h⟩`
  have hinf : ((D'.fam () : Subgroup G) : Set G).Infinite := by
    rw [hD'fam]
    exact infinite_zpowers.mpr hord
  have hgB₁ : g ∈ (D.adjoinPair g).base := Set.mem_union_right _ (Set.mem_insert g _)
  have hgB : g ∈ D'.base := hbase' hgB₁
  have hgH' : g ∉ D'.fam () := by
    rw [hD'fam]
    exact hgH
  obtain ⟨k, hk, hlox⟩ := GGT.exists_isLoxodromic_mul_of_notMem_fam D' hemb'.hyperbolic
    (GGT.not_subset_relBall_of_infinite D' hemb' hinf) hgB hgH'
  have hkH : k ∈ Subgroup.zpowers h := by
    rw [← hD'fam]
    exact hk
  have hkS : k ∈ S := hlt.le hkH
  -- `h` is elliptic of infinite order, so it is outside `E(gk)`
  have hhD' : h ∈ D'.fam () := by
    rw [hD'fam]
    exact Subgroup.mem_zpowers h
  have hSne : ActsNonElementarily S (Cayley.base D'.alphabet) :=
    GGT.Elementary.actsNonElementarily_of_notMem_elementaryClosure
      (isIsometricAction_cayley D'.alphabet)
      (GGT.ElementaryMorse.independentOfNoCommonZpow_cayley_of_hyperbolic D'.alphabet hδ hacy)
      (S.mul_mem hgS hkS) hS hlox
      (GGT.OsinComponents.notMem_elementaryClosure_of_mem_fam' D' () hacy hlox hhD' hord)
  have htop : ActsNonElementarily (⊤ : Subgroup G) (Cayley.base D'.alphabet) := by
    obtain ⟨a, -, b, -, ha, hb, hind⟩ := hSne
    exact ⟨a, Subgroup.mem_top a, b, Subgroup.mem_top b, ha, hb, hind⟩
  refine ⟨⟨D'.alphabet, δ, hδ, hacy, htop⟩, ?_, hSne,
    normalizesNoNontrivialFinite_of_isHyperbolicallyEmbedded D hemb hDfam hord hS⟩
  intro x hx
  have hxD : x ∈ D.base := by
    rw [hbase]
    exact hx
  exact Set.mem_union_left _ (hbase' (GGT.RelGenSet.base_subset_adjoinPair D g hxD))

#audit_closed_axioms printedHullLemma58

end HullTheorem312Lemma58
end NonMF
end Manuscript
end GroupApproximation
