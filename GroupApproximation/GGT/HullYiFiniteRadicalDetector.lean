import GroupApproximation.GGT.HullYiLoxRadical
import GroupApproximation.GGT.ElementaryCoarseTranslationQuasiconvex
import GroupApproximation.GGT.CayleyGeodesicRealisation
import GroupApproximation.GGT.HyperbolicWPDTransfer

/-!
# A finite family detects Hull's loxodromic radical

Hull's proof of Lemma 5.6 first replaces the intersection over every suitable
loxodromic by the intersection of finitely many elementary closures.  This is
not a compactness assertion.  Two independent loxodromics already have finite
elementary-closure intersection; every element of that finite set which is not
in the radical is then excluded by one further loxodromic.

This module proves that reduction at Hull's prescribed Cayley alphabet.  The
virtual-cyclicity input used to make the first intersection finite is also
proved here: pass to the geodesic realization, use the unconditional Morse/WPD
finite-transversal theorem there, and apply the finite pigeonhole theorem.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.GGT.Elementary
open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

variable {G : Type u} [Group G]

/-- Osin's elementwise virtual-cyclicity conclusion for the elementary
closures of loxodromics in Hull's prescribed Cayley graph. -/
theorem elementaryClosureVirtuallyCyclic_hullGeneratingSet
    (A : HullGeneratingSet G) :
    ElementaryClosureVirtuallyCyclic G (Cayley.base A.alphabet) := by
  intro g hg K hKE hKinf
  have hdelta0 : 0 ≤ A.delta :=
    nonneg_of_isHyperbolicSpace A.hyperbolic (Cayley.base A.alphabet)
  let M := CayleyGeodesicModel.modelQuot A.alphabet A.hyperbolic hdelta0
    (CayleyGeodesicModel.isGeodesicRealisationQuot A.alphabet)
  letI : PseudoMetricSpace M.W := M.metric
  letI : MulAction G M.W := M.action
  have hg' : IsLoxodromic g (M.iota (Cayley.base A.alphabet)) :=
    isLoxodromic_map M.distortion_nonneg M.hasAdditiveDistortion M.equivariant hg
  have hwpd : IsWPDAt g (Cayley.base A.alphabet) :=
    isWPDAt_of_isAcylindrical A.acylindrical hg
  have hwpd' : IsWPDAt g (M.iota (Cayley.base A.alphabet)) :=
    isWPDAt_map M.distortion_nonneg M.hasAdditiveDistortion M.equivariant hwpd
  have hfin : ElementaryClosureFiniteTransversal g :=
    exists_finite_transversal_elementaryClosure_of_geodesic
      M.hyperbolic M.delta_nonneg M.geodesic M.isometric hg' hwpd'
  exact exists_nonzero_zpow_mem_of_finiteTransversal hfin K hKE hKinf

/-- A finite set of loxodromics in a suitable subgroup detects its full
loxodromic radical.  The equivalence is pointwise so consumers do not need to
choose an indexing type or manipulate a finite infimum. -/
theorem exists_finite_loxodromic_detector
    (A : HullGeneratingSet G) {S : Subgroup G}
    (hS : Suitable A.alphabet S) :
    ∃ F : Finset G,
      (∀ h ∈ F, h ∈ S ∧ IsLoxodromic h (Cayley.base A.alphabet)) ∧
      ∀ x : G, x ∈ loxRadical A.alphabet S ↔
        ∀ h ∈ F, x ∈ elementaryClosure h := by
  classical
  obtain ⟨a, haS, b, hbS, halox, hblox, hind⟩ := hS.actsNonElementarily
  let I : Subgroup G := elementaryClosure a ⊓ elementaryClosure b
  have hIfin : (I : Set G).Finite := by
    by_contra hIinf
    exact not_infinite_le_inf_elementaryClosure
      (isIsometricAction_cayley A.alphabet)
      (elementaryClosureVirtuallyCyclic_hullGeneratingSet A)
      halox hblox hind (K := I) inf_le_left inf_le_right hIinf
  let B : Set G := (I : Set G) \ (loxRadical A.alphabet S : Set G)
  have hBfin : B.Finite := hIfin.subset fun _ hx => hx.1
  have hexclude : ∀ x : G, x ∈ B → ∃ h : G,
      h ∈ S ∧ IsLoxodromic h (Cayley.base A.alphabet) ∧
        x ∉ elementaryClosure h := by
    intro x hx
    have hxnot : x ∉ loxRadical A.alphabet S := hx.2
    rw [mem_loxRadical] at hxnot
    push Not at hxnot
    exact hxnot
  choose witness hwS hwlox hwexclude using hexclude
  let pick : G → G := fun x => if hx : x ∈ B then witness x hx else 1
  have hpickS : ∀ x ∈ B, pick x ∈ S := by
    intro x hx
    simp only [pick, dif_pos hx]
    exact hwS x hx
  have hpickLox : ∀ x ∈ B,
      IsLoxodromic (pick x) (Cayley.base A.alphabet) := by
    intro x hx
    simp only [pick, dif_pos hx]
    exact hwlox x hx
  have hpickExclude : ∀ x ∈ B, x ∉ elementaryClosure (pick x) := by
    intro x hx
    simp only [pick, dif_pos hx]
    exact hwexclude x hx
  let F : Finset G := {a, b} ∪ hBfin.toFinset.image pick
  have hFdata : ∀ h ∈ F,
      h ∈ S ∧ IsLoxodromic h (Cayley.base A.alphabet) := by
    intro h hh
    rw [Finset.mem_union] at hh
    rcases hh with hh | hh
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with rfl | rfl
      · exact ⟨haS, halox⟩
      · exact ⟨hbS, hblox⟩
    · obtain ⟨x, hxB, rfl⟩ := Finset.mem_image.mp hh
      have hx : x ∈ B := hBfin.mem_toFinset.mp hxB
      exact ⟨hpickS x hx, hpickLox x hx⟩
  refine ⟨F, hFdata, ?_⟩
  · intro x
    constructor
    · intro hx h hh
      have hhdata := hFdata h hh
      exact mem_loxRadical.mp hx h hhdata.1 hhdata.2
    · intro hx
      have hxa : x ∈ elementaryClosure a := hx a (by simp [F])
      have hxb : x ∈ elementaryClosure b := hx b (by simp [F])
      have hxI : x ∈ I := ⟨hxa, hxb⟩
      by_contra hxrad
      have hxB : x ∈ B := ⟨hxI, hxrad⟩
      have hwmem : pick x ∈ F := by
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨x, hBfin.mem_toFinset.mpr hxB, rfl⟩
      exact hpickExclude x hxB (hx (pick x) hwmem)

/-- In a suitable subgroup the finite detector has trivial intersection.  This
is the finite-family-to-radical bridge used in Hull's proof of `yi`. -/
theorem exists_finite_loxodromic_family_trivial_intersection
    (A : HullGeneratingSet G) {S : Subgroup G}
    (hS : Suitable A.alphabet S) :
    ∃ F : Finset G,
      (∀ h ∈ F, h ∈ S ∧ IsLoxodromic h (Cayley.base A.alphabet)) ∧
      ∀ x : G, (∀ h ∈ F, x ∈ elementaryClosure h) → x = 1 := by
  obtain ⟨F, hF, hdetect⟩ := exists_finite_loxodromic_detector A hS
  refine ⟨F, hF, ?_⟩
  intro x hx
  have hxrad : x ∈ loxRadical A.alphabet S := (hdetect x).mpr hx
  rw [loxRadical_eq_bot_of_suitable
    (elementaryClosureVirtuallyCyclic_hullGeneratingSet A) hS,
    Subgroup.mem_bot] at hxrad
  exact hxrad

end HullSC
end GroupApproximation
