import GroupApproximation.Sofic.SoficActionOrbits

/-!
# Quotient actions transported across a group equivalence

A group equivalence carries a subgroup to its image and therefore identifies
the corresponding left-coset actions.  This file records the identification at
the level of sofic actions.
-/

namespace GroupApproximation

universe u

variable {G H : Type u} [Group G] [Group H]

/-- The map on left cosets induced by a group equivalence. -/
def quotientMapMulEquiv (e : G ≃* H) (K : Subgroup G) :
    G ⧸ K → H ⧸ K.map e.toMonoidHom :=
  Quotient.map' (fun g : G => e g) (by
    intro a b hab
    apply QuotientGroup.leftRel_apply.mpr
    have hmem : a⁻¹ * b ∈ K := QuotientGroup.leftRel_apply.mp hab
    have himg : e (a⁻¹ * b) ∈ K.map e.toMonoidHom :=
      Subgroup.mem_map_of_mem e.toMonoidHom hmem
    simpa using himg)

@[simp] theorem quotientMapMulEquiv_mk (e : G ≃* H) (K : Subgroup G) (g : G) :
    quotientMapMulEquiv e K (QuotientGroup.mk g) = QuotientGroup.mk (e g) := rfl

/-- The induced map on cosets is injective. -/
theorem quotientMapMulEquiv_injective (e : G ≃* H) (K : Subgroup G) :
    Function.Injective (quotientMapMulEquiv e K) := by
  intro x y hxy
  induction x using QuotientGroup.induction_on with
  | _ a =>
    induction y using QuotientGroup.induction_on with
    | _ b =>
      rw [quotientMapMulEquiv_mk, quotientMapMulEquiv_mk] at hxy
      have hmem : (e a)⁻¹ * e b ∈ K.map e.toMonoidHom :=
        (QuotientGroup.eq (s := K.map e.toMonoidHom)).mp hxy
      obtain ⟨k, hk, hkEq⟩ := hmem
      have hpre : a⁻¹ * b = k := by
        apply e.injective
        rw [map_mul, map_inv]
        exact hkEq.symm
      exact (QuotientGroup.eq (s := K)).mpr (by rw [hpre]; exact hk)

/-- The induced map on cosets is surjective. -/
theorem quotientMapMulEquiv_surjective (e : G ≃* H) (K : Subgroup G) :
    Function.Surjective (quotientMapMulEquiv e K) := by
  intro y
  induction y using QuotientGroup.induction_on with
  | _ h =>
    refine ⟨QuotientGroup.mk (e.symm h), ?_⟩
    rw [quotientMapMulEquiv_mk, e.apply_symm_apply]

/-- Regard `G/K` as an `H`-set through the inverse group equivalence.
Installed with `letI` at use sites: the equivalence cannot be inferred. -/
def quotientSourceAction (e : G ≃* H) (K : Subgroup G) :
    MulAction H (G ⧸ K) :=
  MulAction.compHom _ e.symm.toMonoidHom

/-- The induced coset map is equivariant for the transported action. -/
theorem quotientMapMulEquiv_equivariant (e : G ≃* H) (K : Subgroup G)
    (h : H) (x : G ⧸ K) :
    quotientMapMulEquiv e K (e.symm h • x)
      = h • quotientMapMulEquiv e K x := by
  induction x using QuotientGroup.induction_on with
  | _ g =>
    show quotientMapMulEquiv e K
        (QuotientGroup.mk (e.symm h * g)) =
      h • QuotientGroup.mk (e g)
    rw [quotientMapMulEquiv_mk, map_mul, e.apply_symm_apply]
    rw [MulAction.Quotient.smul_mk, smul_eq_mul]

/-- **Quotient-action transfer.**  Soficity of `G ↷ G/K` is invariant under a
group equivalence, with the stabilizer transported by subgroup map. -/
theorem isSoficAction_quotient_map_mulEquiv (e : G ≃* H) (K : Subgroup G)
    (hG : IsSoficAction G (G ⧸ K)) :
    IsSoficAction H (H ⧸ K.map e.toMonoidHom) := by
  letI : MulAction H (G ⧸ K) := quotientSourceAction e K
  have hsource : IsSoficAction H (G ⧸ K) := by
    refine IsSoficAction.of_mulEquiv e ?_ hG
    intro g x
    change e.symm (e g) • x = g • x
    rw [e.symm_apply_apply]
  refine isSoficAction_of_equivariant_cover fun E => ?_
  exact ⟨G ⧸ K, inferInstance, quotientMapMulEquiv e K,
    quotientMapMulEquiv_equivariant e K,
    quotientMapMulEquiv_injective e K,
    fun y _ => quotientMapMulEquiv_surjective e K y,
    hsource⟩

end GroupApproximation
