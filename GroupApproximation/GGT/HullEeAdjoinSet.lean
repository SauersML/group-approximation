import GroupApproximation.GGT.HullEeAdjacent

/-!
# Adjoining a finite symmetric set to the base

The last step of Hull's Lemma `ee` compares two relative generating sets whose
bases differ by a **finite** set: `X` against `X ∪ F_n`, where `F_n` is the finite
set of `E`-letters the isolated-component estimate permits.  That comparison is
`GGT.DGOCorollary427`, and to state it one needs the enlarged relative generating
set to exist.  This module builds it.

## Why a set and not a subgroup, and why symmetry has to be arranged

`GGT/HullEeOneStep.lean` already adjoins a **subgroup**, where symmetry of the
base comes free.  `F_n` is not a subgroup --- it is a ball, cut out by a radius
--- so `relGenSetAddSet` takes the symmetry as a hypothesis, and `symmClosure`
supplies it by throwing in the inverses.  That doubles a finite set and leaves it
finite, which is all `DGOCorollary427` asks.

The alternative would be to prove that a relative ball is already symmetric, by
reversing the word that witnesses membership.  The machinery for that exists
(`OsinComponents.avoidsFrom_revWord`), but it is a real argument about avoidance
under reversal, and nothing here needs the sharper fact: the citation is stated
at a finite symmetric difference, and `F_n ∪ F_n⁻¹` is as finite as `F_n`.
Symmetrising is the cheaper of two correct routes.

`GGT/DGOCorollary427PairLocal.adjoinPeripheralSet` is the neighbouring
construction and does **not** serve here: it requires the adjoined set to lie
inside the peripheral family already, which is exactly what `F_n` does not do ---
`F_n` sits inside `E`, and `E` is the subgroup being moved into the base rather
than a member of the family.

## What is proved

The constructor, its base and family, and the one fact the citation consumes:
the symmetric difference of the two bases is contained in the adjoined set, hence
finite when it is.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

section AdjoinSet

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## 1.  Symmetrising a set -/

/-- **A set together with its inverses.** -/
def symmClosure (F : Set G) : Set G := F ∪ ((fun x : G => x⁻¹) '' F)

theorem subset_symmClosure (F : Set G) : F ⊆ symmClosure F :=
  Set.subset_union_left

/-- **The symmetrisation is symmetric**, which is the point of it. -/
theorem inv_mem_symmClosure {F : Set G} {x : G} (hx : x ∈ symmClosure F) :
    x⁻¹ ∈ symmClosure F := by
  rcases hx with hx | ⟨y, hy, rfl⟩
  · exact Or.inr ⟨x, hx, rfl⟩
  · refine Or.inl ?_
    simpa using hy

/-- **And still finite**, being a set and its image under one map. -/
theorem symmClosure_finite {F : Set G} (hF : F.Finite) :
    (symmClosure F).Finite :=
  hF.union (hF.image _)

/-! ## 2.  The enlarged relative generating set -/

/-- **The base enlarged by a symmetric set**, the family untouched.

Symmetry of the adjoined set is a hypothesis rather than a consequence, because
the sets this is used at are relative balls rather than subgroups. -/
def relGenSetAddSet (D : RelGenSet G Λ) (N : Set G) (hN : ∀ x ∈ N, x⁻¹ ∈ N) :
    RelGenSet G Λ where
  base := D.base ∪ N
  fam := D.fam
  symmetricGenerating := by
    refine ⟨?_, ?_⟩
    · rintro x ((hx | hx) | hx)
      · rcases D.symmetricGenerating.inv_mem x (Or.inl hx) with hi | hi
        · exact Or.inl (Or.inl hi)
        · exact Or.inr hi
      · exact Or.inl (Or.inr (hN x hx))
      · rcases D.symmetricGenerating.inv_mem x (Or.inr hx) with hi | hi
        · exact Or.inl (Or.inl hi)
        · exact Or.inr hi
    · refine eq_top_iff.mpr ?_
      rw [← D.symmetricGenerating.closure_eq]
      refine Subgroup.closure_mono ?_
      rintro y (hy | hy)
      · exact Or.inl (Or.inl hy)
      · exact Or.inr hy

@[simp] theorem base_relGenSetAddSet (D : RelGenSet G Λ) (N : Set G)
    (hN : ∀ x ∈ N, x⁻¹ ∈ N) :
    (relGenSetAddSet D N hN).base = D.base ∪ N := rfl

@[simp] theorem fam_relGenSetAddSet (D : RelGenSet G Λ) (N : Set G)
    (hN : ∀ x ∈ N, x⁻¹ ∈ N) : (relGenSetAddSet D N hN).fam = D.fam := rfl

/-! ## 3.  The clause the citation consumes -/

/-- **The two bases differ inside the adjoined set.**

`GGT.DGOCorollary427` asks for a finite symmetric difference; this says the
difference is contained in `N`, so finiteness of `N` is enough and no further
computation of the difference is needed. -/
theorem symmDiff_base_subset (D : RelGenSet G Λ) (N : Set G)
    (hN : ∀ x ∈ N, x⁻¹ ∈ N) :
    ((relGenSetAddSet D N hN).base \ D.base)
        ∪ (D.base \ (relGenSetAddSet D N hN).base) ⊆ N := by
  rintro x (⟨hx1, hx2⟩ | ⟨hx1, hx2⟩)
  · rcases hx1 with hb | hn
    · exact absurd hb hx2
    · exact hn
  · exact absurd (Or.inl hx1 : x ∈ D.base ∪ N) hx2

/-- **So the difference is finite when the adjoined set is**, which is the form
`DGOCorollary427` is applied at. -/
theorem symmDiff_base_finite (D : RelGenSet G Λ) {N : Set G}
    (hN : ∀ x ∈ N, x⁻¹ ∈ N) (hfin : N.Finite) :
    (((relGenSetAddSet D N hN).base \ D.base)
      ∪ (D.base \ (relGenSetAddSet D N hN).base)).Finite :=
  hfin.subset (symmDiff_base_subset D N hN)

end AdjoinSet

end GGT
end GroupApproximation
