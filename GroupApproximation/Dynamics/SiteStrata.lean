import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Union

/-!
# Finite coset covers of marked-site strata

A pointwise stabilizer identifies group elements with the same finite tuple
of inverse images of marked sites. If each inverse image lies in a finite
set, only finitely many right stabilizer cosets are needed. Enlarged strata
have this property with the finite set of translated memory sites.
-/

namespace GroupApproximation.Surjunctivity

universe u v

variable {G : Type u} [Group G] {X : Type v} [MulAction G X]

/-- The subgroup fixing every marked site. -/
def siteStabilizer (U : Finset X) : Subgroup G where
  carrier := {g | ∀ s ∈ U, g • s = s}
  one_mem' := by intro s _; exact one_smul G s
  mul_mem' := by
    intro g h hg hh s hs
    rw [mul_smul, hh s hs, hg s hs]
  inv_mem' := by
    intro g hg s hs
    calc
      g⁻¹ • s = g⁻¹ • (g • s) := congrArg (fun x => g⁻¹ • x) (hg s hs).symm
      _ = s := inv_smul_smul g s

@[simp] theorem mem_siteStabilizer {U : Finset X} {g : G} :
    g ∈ siteStabilizer U ↔ ∀ s ∈ U, g • s = s := Iff.rfl

@[simp] theorem siteStabilizer_empty : siteStabilizer (G := G) (∅ : Finset X) = ⊤ := by
  ext g
  simp [mem_siteStabilizer]

theorem siteStabilizer_antitone {U V : Finset X} (hUV : U ⊆ V) :
    siteStabilizer (G := G) V ≤ siteStabilizer U := by
  intro g hg s hs
  exact hg s (hUV hs)

/-- Equal inverse-image tuples lie in one right stabilizer coset. -/
theorem mul_inv_mem_siteStabilizer {U : Finset X} {g h : G}
    (heq : ∀ s ∈ U, g⁻¹ • s = h⁻¹ • s) : g * h⁻¹ ∈ siteStabilizer U := by
  intro s hs
  rw [mul_smul, ← heq s hs, smul_inv_smul]

/-- A finite tuple of inverse images gives a finite right-coset cover. -/
theorem finite_coset_cover_of_site_images (U D : Finset X) (R : Set G)
    (hR : ∀ g ∈ R, ∀ s ∈ U, g⁻¹ • s ∈ D) :
    ∃ F : Finset G, ∀ g ∈ R, ∃ r ∈ F, g * r⁻¹ ∈ siteStabilizer U := by
  classical
  let code : R → (U → D) := fun g s => ⟨(g : G)⁻¹ • (s : X), hR g g.property s s.property⟩
  let rep : Set.range code → R := fun c => Classical.choose c.property
  have hrep (c : Set.range code) : code (rep c) = c.val := Classical.choose_spec c.property
  let F : Finset G := Finset.univ.image (fun c : Set.range code => (rep c : G))
  refine ⟨F, ?_⟩
  intro g hg
  let c : Set.range code := ⟨code ⟨g, hg⟩, ⟨⟨g, hg⟩, rfl⟩⟩
  refine ⟨rep c, Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩, ?_⟩
  apply mul_inv_mem_siteStabilizer
  intro s hs
  exact (congrArg Subtype.val (congrFun (hrep c) ⟨s, hs⟩)).symm

/-- A group position is on the stratum of `s` when its inverse image is a
memory site. -/
def siteStratum (L : Finset X) (s : X) : Set G := {g | g⁻¹ • s ∈ L}

/-- The region where every marked stratum meets the same finite window. -/
def strataRegion (U L : Finset X) (F : Finset G) : Set G :=
  {g | ∀ s ∈ U, ∃ f ∈ F, g * f ∈ siteStratum L s}

/-- Finite window enlargements of all marked strata still meet only finitely
many right cosets of their common stabilizer. -/
theorem finite_coset_cover_strataRegion (U L : Finset X) (F : Finset G) :
    ∃ T : Finset G, ∀ g ∈ strataRegion U L F,
      ∃ r ∈ T, g * r⁻¹ ∈ siteStabilizer U := by
  classical
  let D : Finset X := F.biUnion (fun f => L.image (fun s => f • s))
  apply finite_coset_cover_of_site_images U D (strataRegion U L F)
  intro g hg s hs
  obtain ⟨f, hf, hgf⟩ := hg s hs
  apply Finset.mem_biUnion.mpr
  refine ⟨f, hf, Finset.mem_image.mpr ⟨(g * f)⁻¹ • s, hgf, ?_⟩⟩
  simp only [mul_inv_rev, mul_smul, smul_inv_smul]

end GroupApproximation.Surjunctivity
