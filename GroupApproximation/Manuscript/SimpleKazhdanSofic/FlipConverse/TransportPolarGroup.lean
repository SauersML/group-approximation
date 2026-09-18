import Mathlib
import GroupApproximation.Meta.AxiomGuard

/-!
# Transport of polars, part 1: isomorphisms transport centralisers

Census row `2e7c7d9ab149` (tex: "for topological full groups the converse holds"), lane
`sk-flip-14`, Rubin route (polar dictionary, Φ-invariant reduction).

Pure group theory.  For a group isomorphism `Φ : G ≃* H` and a subset `A ⊆ G`:

* `map_centralizer_eq`: `Φ '' C(A) = C(Φ '' A)`.
  `⊆`: if `g` commutes with every `a ∈ A`, then `Φ a * Φ g = Φ (a * g) = Φ (g * a) = Φ g * Φ a`.
  `⊇`: if `y` commutes with every `Φ a`, then `Φ.symm y` commutes with every `a`, because `Φ` is
  injective and `Φ (a * Φ.symm y) = Φ a * y = y * Φ a = Φ (Φ.symm y * a)`; and
  `Φ (Φ.symm y) = y` (`MulEquiv.apply_symm_apply`).
* `map_centralizer_centralizer`: `Φ '' C(C(A)) = C(C(Φ '' A))`, applying the first lemma twice.
* `map_eq_centralizer_of_eq_centralizer`: if `B = C(A)` then `Φ '' B = C(Φ '' A)`, so polar
  pairs are carried to polar pairs.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

section TransportCentralizer

variable {G H : Type*} [Group G] [Group H]

/-- A group isomorphism carries the centraliser of a set onto the centraliser of its image. -/
theorem map_centralizer_eq (Φ : G ≃* H) (A : Set G) :
    Φ '' (Subgroup.centralizer A : Set G) = Subgroup.centralizer (Φ '' A) := by
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hg' : ∀ a ∈ A, a * g = g * a := Subgroup.mem_centralizer_iff.1 (SetLike.mem_coe.1 hg)
    refine SetLike.mem_coe.2 (Subgroup.mem_centralizer_iff.2 ?_)
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul Φ a g, ← map_mul Φ g a, hg' a ha]
  · intro hy
    have hy' : ∀ b ∈ Φ '' A, b * y = y * b :=
      Subgroup.mem_centralizer_iff.1 (SetLike.mem_coe.1 hy)
    refine ⟨Φ.symm y, SetLike.mem_coe.2 (Subgroup.mem_centralizer_iff.2 fun a ha => ?_),
      Φ.apply_symm_apply y⟩
    apply Φ.injective
    rw [map_mul Φ a (Φ.symm y), map_mul Φ (Φ.symm y) a, Φ.apply_symm_apply y]
    exact hy' (Φ a) (Set.mem_image_of_mem Φ ha)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.map_centralizer_eq

/-- A group isomorphism carries the double centraliser (the polar closure) of a set onto the
double centraliser of its image. -/
theorem map_centralizer_centralizer (Φ : G ≃* H) (A : Set G) :
    Φ '' (Subgroup.centralizer (Subgroup.centralizer A : Set G) : Set G) =
      Subgroup.centralizer (Subgroup.centralizer (Φ '' A) : Set H) := by
  rw [map_centralizer_eq Φ (Subgroup.centralizer A : Set G), map_centralizer_eq Φ A]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.map_centralizer_centralizer

/-- If `B` is the centraliser of `A`, then `Φ '' B` is the centraliser of `Φ '' A`. -/
theorem map_eq_centralizer_of_eq_centralizer (Φ : G ≃* H) {A B : Set G}
    (hB : B = Subgroup.centralizer A) :
    Φ '' B = Subgroup.centralizer (Φ '' A) := by
  rw [hB, map_centralizer_eq Φ A]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.map_eq_centralizer_of_eq_centralizer

end TransportCentralizer

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse
