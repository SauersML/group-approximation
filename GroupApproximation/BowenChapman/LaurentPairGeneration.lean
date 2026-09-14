import GroupApproximation.BowenChapman.LaurentPairKazhdan
import GroupApproximation.Leavitt.ElementaryFinitelyGeneratedRing

/-!
# Finite generation and countability of the Bowen--Chapman ambient group

`Ambient = EL₃(𝔽₂[ℤ³]) ⋊ EL₃(ℤ)` is finitely generated and countable.

Both facts come from the factors.  An elementary group of rank three over a
finitely generated ring is finitely generated
(`elementaryGroup_finitelyGenerated_of_isFinitelyGeneratedRing`), and the images
of generating sets of the two factors generate the semidirect product, because
every element is `inl a * inr b`.  An elementary group over a countable ring is
countable, since a unit of the matrix ring is determined by its matrix, and a
semidirect product is in bijection with the product of its factors.
-/

namespace GroupApproximation

/-- A semidirect product of finitely generated groups is finitely generated. -/
theorem group_fg_semidirectProduct {N Q : Type*} [Group N] [Group Q]
    (φ : Q →* MulAut N) (hN : Group.FG N) (hQ : Group.FG Q) :
    Group.FG (SemidirectProduct N Q φ) := by
  classical
  obtain ⟨SN, hSN⟩ := Group.fg_def.mp hN
  obtain ⟨SQ, hSQ⟩ := Group.fg_def.mp hQ
  let T : Finset (SemidirectProduct N Q φ) :=
    SN.image (SemidirectProduct.inl : N →* SemidirectProduct N Q φ) ∪
      SQ.image (SemidirectProduct.inr : Q →* SemidirectProduct N Q φ)
  refine Group.fg_def.mpr ⟨T, ?_⟩
  have hinl : ∀ n : N,
      (SemidirectProduct.inl n : SemidirectProduct N Q φ) ∈
        Subgroup.closure (T : Set (SemidirectProduct N Q φ)) := by
    intro n
    have hn : n ∈ Subgroup.closure (SN : Set N) := by
      rw [hSN]
      exact Subgroup.mem_top n
    have hmem := Subgroup.mem_map_of_mem
      (SemidirectProduct.inl : N →* SemidirectProduct N Q φ) hn
    rw [MonoidHom.map_closure] at hmem
    refine Subgroup.closure_mono ?_ hmem
    rintro _ ⟨m, hm, rfl⟩
    exact Finset.mem_coe.mpr
      (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_coe.mp hm)))
  have hinr : ∀ q : Q,
      (SemidirectProduct.inr q : SemidirectProduct N Q φ) ∈
        Subgroup.closure (T : Set (SemidirectProduct N Q φ)) := by
    intro q
    have hq : q ∈ Subgroup.closure (SQ : Set Q) := by
      rw [hSQ]
      exact Subgroup.mem_top q
    have hmem := Subgroup.mem_map_of_mem
      (SemidirectProduct.inr : Q →* SemidirectProduct N Q φ) hq
    rw [MonoidHom.map_closure] at hmem
    refine Subgroup.closure_mono ?_ hmem
    rintro _ ⟨m, hm, rfl⟩
    exact Finset.mem_coe.mpr
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_coe.mp hm)))
  rw [eq_top_iff]
  intro x _
  rw [← SemidirectProduct.inl_left_mul_inr_right x]
  exact mul_mem (hinl x.left) (hinr x.right)

/-- A semidirect product of countable groups is countable. -/
theorem countable_semidirectProduct {N Q : Type*} [Group N] [Group Q]
    (φ : Q →* MulAut N) [Countable N] [Countable Q] :
    Countable (SemidirectProduct N Q φ) :=
  (SemidirectProduct.equivProd : SemidirectProduct N Q φ ≃ N × Q).injective.countable

/-- The elementary group of rank `n` over a countable ring is countable. -/
theorem countable_elementaryGroup_fin (R : Type*) [Ring R] [Countable R] (n : ℕ) :
    Countable ↥(elementaryGroup (Fin n) R) := by
  haveI : Countable (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (Countable (Fin n → Fin n → R))
  haveI : Countable (Matrix (Fin n) (Fin n) R)ˣ := Units.val_injective.countable
  infer_instance

namespace BowenChapman

/-- **The ambient group is finitely generated.** -/
theorem ambient_fg : Group.FG Ambient :=
  group_fg_semidirectProduct actorAction
    (elementaryGroup_finitelyGenerated_of_isFinitelyGeneratedRing
      isFinitelyGeneratedRing_laurent 3 (by norm_num))
    (elementaryGroup_finitelyGenerated_of_isFinitelyGeneratedRing
      isFinitelyGeneratedRing_int 3 (by norm_num))

/-- `𝔽₂[ℤ³]` is countable. -/
instance laurent_countable : Countable Laurent := by
  haveI : Countable (ZMod 2) := Finite.to_countable
  exact AddMonoidAlgebra.coeff_injective.countable

/-- **The ambient group is countable.** -/
instance ambient_countable : Countable Ambient := by
  haveI := countable_elementaryGroup_fin Laurent 3
  haveI := countable_elementaryGroup_fin ℤ 3
  exact countable_semidirectProduct actorAction

end BowenChapman

end GroupApproximation
