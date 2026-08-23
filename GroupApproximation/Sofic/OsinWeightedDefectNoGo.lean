import GroupApproximation.Sofic.OsinWeightedMetric

/-!
# The weighted relative lane cannot saturate a source defect

The weighted metric repairs the *partner-surjectivity* obstruction of the
whole-syllable lane, but it deliberately keeps every element of the source
factor peripheral.  Consequently its Greendlinger bound embeds the entire
source factor.  This is incompatible with asking a subgroup of that factor to
fill the quotient while a nonidentity source element survives: saturation
makes the source map onto, and partner surjectivity then forces some light
partner generator to agree with a nonidentity source element.  Their difference
has relative length at most two, contradicting the relator floor.

This is a structural no-go theorem for the existing
`WeightedRouterDesign` API.  In particular, an explicit router for the affine
congruence source cannot be obtained by adding a defect-surjectivity field to
that structure.  The absolute avatar construction does not have this problem:
it protects only the designated element rather than embedding the entire source
factor.
-/

namespace GroupApproximation
namespace OsinWeightedMetric

open Monoid Monoid.CoprodI OsinSmallCancellation

namespace WeightedRouterDesign

variable {U B : Type} [Group U] [Group B]
  {G : Bool → Type} [∀ b, Group (G b)]
  (D : WeightedRouterDesign U B G)

/-- If a subgroup of the source fills the routed quotient, then the source map
itself is onto.  This elementary observation is the first half of the no-go
argument. -/
theorem emb_surjective_of_subgroup_map_eq_top (N : Subgroup U)
    (hN : N.map D.emb = ⊤) : Function.Surjective D.emb := by
  intro q
  have hq : q ∈ N.map D.emb := by
    rw [hN]
    exact Subgroup.mem_top q
  rcases hq with ⟨u, hu, rfl⟩
  exact ⟨u, rfl⟩

/-- A generating tuple cannot be killed pointwise by a homomorphism that has a
nonidentity value. -/
theorem exists_generator_not_mem_ker {k : ℕ} (gen : Fin k → B)
    (hgen : Subgroup.closure (Set.range gen) = ⊤) {b : B}
    (hb : D.partnerHom b ≠ 1) :
    ∃ j : Fin k, D.partnerHom (gen j) ≠ 1 := by
  by_contra h
  push Not at h
  have hle : Subgroup.closure (Set.range gen) ≤ D.partnerHom.ker := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact MonoidHom.mem_ker.mpr (h j)
  rw [hgen] at hle
  exact hb (MonoidHom.mem_ker.mp (hle (Subgroup.mem_top b)))

/-- **No defect saturation in the weighted relative router.**

Assume the partner is equipped with a finite generating tuple whose images are
letters for the design's relative metric.  If the weighted Greendlinger leaf
holds and the source is nontrivial, no subgroup of the source can map onto the
routed quotient.

The proof uses only conclusions already exposed by the design:

* the leaf and the floor embed the source;
* the tie makes the partner map onto;
* defect saturation would make the source map onto as well;
* hence a light partner generator agrees with a nonidentity source element;
* `not_relativeLengthBound_of_light_tie` contradicts the length bound.
-/
theorem subgroup_map_ne_top_of_light_partner_generators
    (hleafG : WeightedGreendlingerLeaf D.relLength D.relators (1 / 7))
    {k : ℕ} (gen : Fin k → B)
    (hgen : Subgroup.closure (Set.range gen) = ⊤)
    (hlight : ∀ j : Fin k,
      D.relLength.len (CoprodI.of (D.partnerEquiv (gen j))) ≤ 1)
    (N : Subgroup U) {s : U} (hs : s ≠ 1) :
    N.map D.emb ≠ ⊤ := by
  intro htop
  have hinj : Function.Injective D.emb := D.emb_injective hleafG
  have hs_image : D.emb s ≠ 1 := by
    intro hs1
    apply hs
    apply hinj
    rw [hs1, map_one]
  obtain ⟨b, hb⟩ := D.partnerHom_surjective (D.emb s)
  have hb_ne : D.partnerHom b ≠ 1 := by simpa [hb] using hs_image
  obtain ⟨j, hj⟩ := D.exists_generator_not_mem_ker gen hgen hb_ne
  obtain ⟨u, hu⟩ := D.emb_surjective_of_subgroup_map_eq_top N htop
    (D.partnerHom (gen j))
  have hu_ne : u ≠ 1 := by
    intro hu1
    apply hj
    rw [← hu, hu1, map_one]
  have hx_ne : D.sourceEquiv u ≠ 1 := by
    intro hx
    apply hu_ne
    apply D.sourceEquiv.injective
    rw [hx, map_one]
  have heq :
      factorMap (letterRelatorSubgroup D.relators) false (D.sourceEquiv u) =
        factorMap (letterRelatorSubgroup D.relators) true
          (D.partnerEquiv (gen j)) := by
    exact hu
  have htie :
      CoprodI.of (D.sourceEquiv u) *
          (CoprodI.of (D.partnerEquiv (gen j)))⁻¹ ∈
        letterRelatorSubgroup D.relators := by
    rw [← QuotientGroup.eq_one_iff]
    have hquot : QuotientGroup.mk' (letterRelatorSubgroup D.relators)
        (CoprodI.of (D.sourceEquiv u) *
          (CoprodI.of (D.partnerEquiv (gen j)))⁻¹) = 1 := by
      rw [map_mul, map_inv, heq, mul_inv_cancel]
    exact hquot
  have hfloor : ∀ r ∈ D.relators, 4 ≤ r.length := by
    intro r hr
    exact le_trans (by decide) (D.relators_long r hr)
  exact
    (not_relativeLengthBound_of_light_tie hx_ne (hlight j) hfloor htie)
      (D.lengthBound hleafG)

end WeightedRouterDesign

end OsinWeightedMetric
end GroupApproximation
