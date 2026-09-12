import GroupApproximation.Dynamics.Surjunctivity
import GroupApproximation.Dynamics.Transplant
import GroupApproximation.Algebra.FiniteResidual

/-!
# Residually finite groups are surjunctive

Finite-index normal subgroups simultaneously separate finite sets. An
equivariant map on the full shift preserves configurations pulled back from
each finite quotient. Its injectivity therefore gives bijectivity on every
finite quotient configuration space. The separating-family transplant
theorem then gives surjectivity on the full shift.
-/

namespace GroupApproximation

universe u v w

variable {G : Type u} [Group G]

/-- A finite collection of nonidentity elements avoids one finite-index normal subgroup. -/
theorem IsResiduallyFinite.exists_normal_avoiding_finset (hG : IsResiduallyFinite G)
    (E : Finset G) (hE : ∀ x ∈ E, x ≠ 1) :
    ∃ N : Subgroup G, N.Normal ∧ N.FiniteIndex ∧ ∀ x ∈ E, x ∉ N := by
  classical
  induction E using Finset.induction_on with
  | empty =>
      exact ⟨⊤, inferInstance, inferInstance, by simp⟩
  | @insert x E hx ih =>
      obtain ⟨N, hNn, hNf, hN⟩ := ih (fun y hy ↦ hE y (Finset.mem_insert_of_mem hy))
      obtain ⟨L, hLf, hxL⟩ := isResiduallyFinite_iff.mp hG x
        (hE x (Finset.mem_insert_self x E))
      letI := hNn
      letI := hNf
      letI := hLf
      refine ⟨L.normalCore ⊓ N, inferInstance, inferInstance, ?_⟩
      intro y hy hmem
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hxL (L.normalCore_le hmem.1)
      · exact hN y hy hmem.2

/-- Every finite set injects into a finite quotient of a residually finite group. -/
theorem IsResiduallyFinite.exists_normal_finiteIndex_injOn (hG : IsResiduallyFinite G)
    (F : Finset G) :
    ∃ N : Subgroup G, N.Normal ∧ N.FiniteIndex ∧
      Set.InjOn (QuotientGroup.mk : G → G ⧸ N) (F : Set G) := by
  classical
  let E := ((F.product F).image fun p : G × G ↦ p.1 / p.2).filter (· ≠ 1)
  obtain ⟨N, hNn, hNf, hN⟩ := hG.exists_normal_avoiding_finset E
    (fun x hx ↦ (Finset.mem_filter.mp hx).2)
  letI := hNn
  refine ⟨N, hNn, hNf, ?_⟩
  intro x hx y hy hxy
  by_contra hne
  have hdiv : x / y ≠ 1 := fun h ↦ hne (div_eq_one.mp h)
  have hmem : x / y ∈ E := Finset.mem_filter.mpr
    ⟨Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩, hdiv⟩
  exact hN (x / y) hmem (QuotientGroup.eq_iff_div_mem.mp hxy)

namespace Surjunctivity

variable {Q : Type v} [Group Q] {B : Type w}

/-- Equivariance preserves the property of factoring through a group homomorphism. -/
theorem equivariant_pullback_fiber_eq (f : G →* Q)
    {τ : (G → B) → (G → B)} (heq : IsEquivariant τ) (y : Q → B)
    {g h : G} (hgh : f g = f h) :
    τ (configPullback f y) g = τ (configPullback f y) h := by
  have hx : shift (g * h⁻¹) (configPullback f y) = configPullback f y := by
    funext a
    simp only [shift, configPullback, Function.comp_apply, map_mul, map_inv, hgh,
      mul_inv_cancel, one_mul]
  have ht := congrFun (heq (g * h⁻¹) (configPullback f y)) h
  rw [hx] at ht
  simpa [shift, mul_assoc] using ht.symm

/-- The map induced on configurations over a surjective group image. -/
noncomputable def homTransplant (f : G →* Q) (hf : Function.Surjective f)
    (τ : (G → B) → (G → B)) (y : Q → B) : Q → B :=
  fun q ↦ τ (configPullback f y) (Function.surjInv hf q)

/-- The representative formula intertwines exactly with pullback. -/
theorem homTransplant_intertwining (f : G →* Q) (hf : Function.Surjective f)
    {τ : (G → B) → (G → B)} (heq : IsEquivariant τ) (y : Q → B) :
    τ (configPullback f y) = configPullback f (homTransplant f hf τ y) := by
  funext g
  exact equivariant_pullback_fiber_eq f heq y (Function.surjInv_eq hf (f g)).symm

/-- On a finite group image, an injective equivariant map induces a surjective map. -/
theorem homTransplant_surjective [Finite Q] [Finite B]
    (f : G →* Q) (hf : Function.Surjective f)
    {τ : (G → B) → (G → B)} (heq : IsEquivariant τ) (hinj : Function.Injective τ) :
    Function.Surjective (homTransplant f hf τ) :=
  Finite.surjective_of_injective
    (transplant_injective hf (homTransplant_intertwining f hf heq) hinj)

/-- Residual finiteness implies surjunctivity, via finite periodic configurations. -/
theorem isSurjunctive_of_isResiduallyFinite (hG : IsResiduallyFinite G) :
    IsSurjunctive G := by
  intro B _ _ _ τ hcont heq hinj
  let I := {N : Subgroup G // N.Normal ∧ N.FiniteIndex}
  letI (i : I) : i.1.Normal := i.2.1
  letI (i : I) : i.1.FiniteIndex := i.2.2
  let Ω : I → Type u := fun i ↦ G ⧸ i.1
  let f (i : I) : G →* Ω i := QuotientGroup.mk' i.1
  have hf (i : I) : Function.Surjective (f i) := QuotientGroup.mk'_surjective i.1
  let τΩ (i : I) : (Ω i → B) → (Ω i → B) := homTransplant (f i) (hf i) τ
  apply transplant_surjective_finite (fun i ↦ f i) hf τ τΩ hcont
  · exact fun i ↦ homTransplant_intertwining (f i) (hf i) heq
  · intro F
    obtain ⟨N, hNn, hNf, hN⟩ := hG.exists_normal_finiteIndex_injOn F
    exact ⟨⟨N, hNn, hNf⟩, hN⟩
  · intro i
    exact homTransplant_surjective (f i) (hf i) heq hinj

end Surjunctivity

end GroupApproximation
