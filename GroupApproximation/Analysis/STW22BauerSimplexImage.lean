import GroupApproximation.Analysis.STW22BauerSimplex
import GroupApproximation.Meta.AxiomGuard

/-!
# Transport of the full Choquet--Bauer property along a linear injection

The existing extreme-boundary transport is extended here to the lattice-cone
clause.  The proof explicitly transports the cone order through the injective
map; no representation theorem is assumed.
-/

namespace GroupApproximation
namespace STW22

open Set

set_option linter.unusedSectionVars false

section

variable {k : Type*} [Semiring k] [PartialOrder k]
variable {E F : Type*} [AddCommMonoid E] [SMul k E]
  [AddCommMonoid F] [SMul k F]

private def conePairMap (e : E → F) : E × k → F × k :=
  fun p ↦ (e p.1, p.2)

private theorem conePairMap_injective (e : E → F)
    (hinj : Function.Injective e) :
    Function.Injective (conePairMap (k := k) e) := by
  intro p q hpq
  apply Prod.ext
  · exact hinj (congrArg Prod.fst hpq)
  · exact congrArg (fun r : F × k ↦ r.2) hpq

private theorem conePairMap_add (e : E → F)
    (hadd : ∀ x y : E, e (x + y) = e x + e y) (p q : E × k) :
    conePairMap e (p + q) = conePairMap e p + conePairMap e q := by
  apply Prod.ext
  · exact hadd p.1 q.1
  · rfl

private theorem conePairMap_cone
    (e : E → F)
    (hsmul : ∀ (c : k) (x : E), e (c • x) = c • e x)
    (S : Set E) :
    conePairMap e '' coneOver k S = coneOver k (e '' S) := by
  ext p
  constructor
  · rintro ⟨q, ⟨t, x, hx, ht, rfl⟩, rfl⟩
    exact ⟨t, e x, ⟨x, hx, rfl⟩, ht, by
      apply Prod.ext
      · exact hsmul t x
      · rfl⟩
  · rintro ⟨t, y, ⟨x, hx, rfl⟩, ht, rfl⟩
    refine ⟨(t • x, t), ⟨t, x, hx, ht, rfl⟩, ?_⟩
    apply Prod.ext
    · exact hsmul t x
    · rfl

private theorem coneLE_conePairMap_iff
    (e : E → F) (hinj : Function.Injective e)
    (hadd : ∀ x y : E, e (x + y) = e x + e y)
    (hsmul : ∀ (c : k) (x : E), e (c • x) = c • e x)
    (S : Set E) (u v : E × k) :
    coneLE k (coneOver k (e '' S)) (conePairMap e u) (conePairMap e v) ↔
      coneLE k (coneOver k S) u v := by
  constructor
  · rintro ⟨c, hc, heq⟩
    rw [← conePairMap_cone e hsmul S] at hc
    obtain ⟨d, hd, rfl⟩ := hc
    refine ⟨d, hd, ?_⟩
    apply conePairMap_injective e hinj
    rw [conePairMap_add e hadd u d]
    exact heq
  · rintro ⟨c, hc, rfl⟩
    refine ⟨conePairMap e c, ?_, ?_⟩
    · rw [← conePairMap_cone e hsmul S]
      exact mem_image_of_mem _ hc
    · exact conePairMap_add e hadd u c

/-- The lattice-cone Choquet condition transports along an injective additive
homogeneous map. -/
theorem IsChoquetSimplex.image
    {S : Set E} (h : IsChoquetSimplex k S)
    (e : E → F) (hinj : Function.Injective e)
    (hadd : ∀ x y : E, e (x + y) = e x + e y)
    (hsmul : ∀ (c : k) (x : E), e (c • x) = c • e x) :
    IsChoquetSimplex k (e '' S) := by
  intro u hu v hv
  rw [← conePairMap_cone e hsmul S] at hu hv
  obtain ⟨u₀, hu₀, rfl⟩ := hu
  obtain ⟨v₀, hv₀, rfl⟩ := hv
  obtain ⟨w₀, hw₀, huw, hvw, hleast⟩ := h u₀ hu₀ v₀ hv₀
  refine ⟨conePairMap e w₀, ?_, ?_, ?_, ?_⟩
  · rw [← conePairMap_cone e hsmul S]
    exact mem_image_of_mem _ hw₀
  · exact (coneLE_conePairMap_iff e hinj hadd hsmul S u₀ w₀).2 huw
  · exact (coneLE_conePairMap_iff e hinj hadd hsmul S v₀ w₀).2 hvw
  · intro z hz huz hvz
    rw [← conePairMap_cone e hsmul S] at hz
    obtain ⟨z₀, hz₀, rfl⟩ := hz
    apply (coneLE_conePairMap_iff e hinj hadd hsmul S w₀ z₀).2
    exact hleast z₀ hz₀
      ((coneLE_conePairMap_iff e hinj hadd hsmul S u₀ z₀).1 huz)
      ((coneLE_conePairMap_iff e hinj hadd hsmul S v₀ z₀).1 hvz)

/-- Every clause of a Bauer simplex transports along a continuous injective
additive homogeneous map. -/
theorem IsBauerSimplex.image
    [TopologicalSpace E] [TopologicalSpace F] [T2Space F]
    {S : Set E} (h : IsBauerSimplex k S)
    (e : E → F) (hcont : Continuous e) (hinj : Function.Injective e)
    (hadd : ∀ x y : E, e (x + y) = e x + e y)
    (hsmul : ∀ (c : k) (x : E), e (c • x) = c • e x) :
    IsBauerSimplex k (e '' S) :=
  ⟨h.1.image e hinj hadd hsmul,
    h.2.image e hcont hinj hadd hsmul⟩

end

end STW22
end GroupApproximation
