import GroupApproximation.GGT.AH3GeodesicCayley
import GroupApproximation.GGT.DGOTheorem442Proof
import GroupApproximation.GGT.HyperbolicAdditiveTransfer
import GroupApproximation.GGT.WPDElement
import GroupApproximation.Manuscript.NonMF.AcylindricallyHyperbolic

/-!
# Osin's definition of acylindrical hyperbolicity, and Hull's Theorem 3.12

`non_mf_groups_exist.tex` uses *acylindrically hyperbolic* in Osin's sense: a
group admitting a non-elementary acylindrical isometric action on a (geodesic)
hyperbolic space.  For acylindrical actions Osin's Theorem 1.1 makes
non-elementarity equivalent to containing two independent loxodromic elements,
and that is the spelling used here (`IsAcylindricallyHyperbolicOsin`); the
limit-set spelling is `SequentialBoundary.IsAcylindricallyHyperbolicLimitSet`.

The repository works with Hull's Cayley-graph form,
`TorsionFree.IsAcylindricallyHyperbolic`.  `isAcylindricallyHyperbolic_iff_osin`
proves the two agree, from landed theorems only:

* **Osin ⇒ Cayley** — a loxodromic element of an acylindrical action is WPD
  (`isWPDAt_of_isAcylindrical`), two independent loxodromics make `G` not
  virtually cyclic (`HullSC.not_isVirtuallyCyclic_of_actsNonElementarily`), and
  Osin's Theorem 1.2 `(AH₃) ⇒ (AH₁)` is `Elementary.osinTheorem12_unconditional`.
* **Cayley ⇒ Osin** — the geodesic realization of Hull's Cayley graph
  (`CayleyGeodesicModel.modelQuot`) is geodesic and hyperbolic, the translation
  action on it is isometric, acylindricity passes to it along the vertex map with
  dense image (`isAcylindrical_of_additiveDistortion_of_dense`), and so do
  loxodromy and independence (`isLoxodromic_map`, `independent_map`).

`exists_hullGeneratingSet_of_osin` is the manuscript's *"choose the generating
set `A` provided by Hull [Theorem 3.12]"* for a group acylindrically hyperbolic in
Osin's sense.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

/-- **Osin's definition of an acylindrically hyperbolic group**: `G` admits an
acylindrical isometric action on a geodesic hyperbolic space that is
non-elementary, spelled as containing two independent loxodromic elements
(Osin, *Acylindrically hyperbolic groups*, Definition 1.3 with Theorem 1.1). -/
def IsAcylindricallyHyperbolicOsin (G : Type) [Group G] : Prop :=
  ∃ (X : Type) (_ : PseudoMetricSpace X) (_ : MulAction G X),
    IsIsometricAction G X ∧ IsGeodesicSpace X ∧ (∃ δ : ℝ, IsHyperbolicSpace δ X) ∧
      IsAcylindrical G X ∧ ∃ x : X, ActsNonElementarily (⊤ : Subgroup G) x

/-- **Osin's notion gives Hull's Cayley-graph notion**, through Osin's Theorem 1.2
`(AH₃) ⇒ (AH₁)`. -/
theorem isAcylindricallyHyperbolic_of_osin {G : Type} [Group G]
    (h : IsAcylindricallyHyperbolicOsin G) : IsAcylindricallyHyperbolic G := by
  obtain ⟨X, instX, instA, hiso, hgeo, ⟨δ, hδ⟩, hacy, x, hne⟩ := h
  letI := instX
  letI := instA
  have hnvc : ¬ IsVirtuallyCyclic G :=
    HullSC.not_isVirtuallyCyclic_of_actsNonElementarily hiso hne
  obtain ⟨g, -, _, -, hg, -, -⟩ := hne
  have hwpd : IsWPDAt g x := isWPDAt_of_isAcylindrical hacy hg
  exact Elementary.osinTheorem12_unconditional G
    (AH3Data.ofData X hiso δ hδ hgeo g x hg hwpd) hnvc

/-- **Hull's Cayley-graph notion gives Osin's notion**, on the geodesic realization
of the Cayley graph. -/
theorem osin_of_isAcylindricallyHyperbolic (G : Type) [Group G]
    [h : IsAcylindricallyHyperbolic G] : IsAcylindricallyHyperbolicOsin G := by
  obtain ⟨A, δ, hδ, hacy, hne⟩ := h.out
  have hδ0 : 0 ≤ δ := by
    have hbase := hδ (Cayley.base A) (Cayley.base A) (Cayley.base A)
      (Cayley.base A)
    rw [min_self] at hbase
    linarith
  let M := CayleyGeodesicModel.modelQuot A hδ hδ0
    (CayleyGeodesicModel.isGeodesicRealisationQuot A)
  letI : PseudoMetricSpace M.W := M.metric
  letI : MulAction G M.W := M.action
  obtain ⟨g, hgmem, k, hkmem, hglox, hklox, hind⟩ := hne
  refine ⟨M.W, M.metric, M.action, M.isometric, M.geodesic, ⟨M.delta, M.hyperbolic⟩,
    isAcylindrical_of_additiveDistortion_of_dense M.distortion_nonneg
      M.hasAdditiveDistortion M.hasDenseImage M.equivariant M.isometric hacy,
    M.iota (Cayley.base A), g, hgmem, k, hkmem, ?_, ?_, ?_⟩
  · exact isLoxodromic_map M.distortion_nonneg M.hasAdditiveDistortion M.equivariant hglox
  · exact isLoxodromic_map M.distortion_nonneg M.hasAdditiveDistortion M.equivariant hklox
  · exact independent_map M.hasAdditiveDistortion M.equivariant hind

/-- **The two definitions agree.** -/
theorem isAcylindricallyHyperbolic_iff_osin (G : Type) [Group G] :
    IsAcylindricallyHyperbolic G ↔ IsAcylindricallyHyperbolicOsin G :=
  ⟨fun h => @osin_of_isAcylindricallyHyperbolic G _ h, isAcylindricallyHyperbolic_of_osin⟩

/-- **Hull, Theorem 3.12, as the manuscript uses it** (tex line 1629): a group
acylindrically hyperbolic in Osin's sense has a generating set `A` whose Cayley
graph is hyperbolic, with the translation action acylindrical and
non-elementary. -/
theorem exists_hullGeneratingSet_of_osin (G : Type) [Group G]
    (h : IsAcylindricallyHyperbolicOsin G) : Nonempty (HullGeneratingSet G) :=
  @exists_hullGeneratingSet G _ (isAcylindricallyHyperbolic_of_osin h)

end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.isAcylindricallyHyperbolic_of_osin
#audit_axioms GroupApproximation.GGT.osin_of_isAcylindricallyHyperbolic
#audit_axioms GroupApproximation.GGT.isAcylindricallyHyperbolic_iff_osin
#audit_axioms GroupApproximation.GGT.exists_hullGeneratingSet_of_osin
