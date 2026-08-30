import GroupApproximation.GGT.ElementaryCoarseTranslationQuasiconvex

/-!
# Consequences of the finite-index conclusion of DGO Lemma 6.5

The published conclusion `[E(h) : ⟨h⟩] < ∞` is represented by
`ElementaryClosureFiniteTransversal`.  This file derives the three facts used
in DGO Theorem 6.8: uniform closeness of the two basepoint orbits,
quasiconvexity, and properness.  It also derives `E(h) ≠ G` when `G` is not
virtually cyclic.
-/

namespace GroupApproximation
namespace GGT
namespace Elementary

open GroupApproximation.HullGeometry

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
  [MulAction G X]

/-- A finite cyclic transversal makes the elementary-closure orbit uniformly
close to the power orbit. -/
theorem elementaryClosureOrbitClose_of_finiteTransversal
    (hiso : IsIsometricAction G X) {h : G} {x : X}
    (hfin : ElementaryClosureFiniteTransversal h) :
    ElementaryClosureOrbitClose h x := by
  obtain ⟨F, hF, hcover⟩ := hfin
  obtain ⟨R, hR⟩ := (hF.image fun f : G => dist x (f • x)).bddAbove
  refine ⟨max 0 R, le_max_left _ _, ?_⟩
  intro g hg
  obtain ⟨c, f, hf, rfl⟩ := hcover g hg
  refine ⟨c, ?_⟩
  have hm := hiso (h ^ c) x (f • x)
  calc
    dist ((h ^ c) • x) ((h ^ c * f) • x) = dist x (f • x) := by
      simpa only [← mul_smul] using hm
    _ ≤ max 0 R := (hR ⟨f, hf, rfl⟩).trans (le_max_right _ _)

/-- A finite cyclic transversal and loxodromy make the elementary closure act
properly at the basepoint. -/
theorem actsProperlyAt_elementaryClosure_of_finiteTransversal
    (hiso : IsIsometricAction G X) {h : G} {x : X}
    (hlox : IsLoxodromic h x)
    (hfin : ElementaryClosureFiniteTransversal h) :
    ActsProperlyAt (elementaryClosure h) x := by
  obtain ⟨F, hF, hcover⟩ := hfin
  intro eps
  refine Set.Finite.subset
    (hF.biUnion fun f _ =>
      (finite_zpow_displacement hiso hlox (eps + dist x (f • x))).image
        (fun c : ℤ => h ^ c * f)) ?_
  rintro g ⟨hgE, hgmove⟩
  obtain ⟨c, f, hf, rfl⟩ := hcover g hgE
  have hpow : dist x ((h ^ c) • x) ≤ eps + dist x (f • x) := by
    have htri := dist_triangle x ((h ^ c * f) • x) ((h ^ c) • x)
    have heq : dist ((h ^ c * f) • x) ((h ^ c) • x) = dist (f • x) x := by
      have hm := hiso (h ^ c) (f • x) x
      simpa only [← mul_smul] using hm
    rw [heq, dist_comm (f • x) x] at htri
    linarith
  exact Set.mem_iUnion.mpr ⟨f, Set.mem_iUnion.mpr ⟨hf, ⟨c, hpow, rfl⟩⟩⟩

/-- A finite cyclic transversal makes `E(h)` proper whenever the ambient group
is not virtually cyclic. -/
theorem elementaryClosure_ne_top_of_finiteTransversal {h : G}
    (hfin : ElementaryClosureFiniteTransversal h)
    (hnvc : ¬ IsVirtuallyCyclic G) : elementaryClosure h ≠ ⊤ := by
  obtain ⟨F, hF, hcover⟩ := hfin
  intro htop
  apply hnvc
  refine isVirtuallyCyclic_of_finite_transversal (h := h) hF ?_
  intro a
  apply hcover a
  rw [htop]
  trivial

/-- The finite-index conclusion of DGO Lemma 6.5 implies quasiconvexity of the
elementary-closure orbit. -/
theorem isQuasiconvexOrbitAt_elementaryClosure_of_finiteTransversal
    {δ : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hiso : IsIsometricAction G X) {h : G} {x : X}
    (hlox : IsLoxodromic h x)
    (hfin : ElementaryClosureFiniteTransversal h) :
    IsQuasiconvexOrbitAt (elementaryClosure h) x :=
  isQuasiconvexOrbitAt_elementaryClosure_of_orbitClose hδ hδ0 hiso hlox
    (elementaryClosureOrbitClose_of_finiteTransversal hiso hfin)

end Elementary
end GGT
end GroupApproximation
