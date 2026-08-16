import GroupApproximation.Algebra.FiniteResidual

/-!
# The finite residual as a commensurability invariant

Sections 49--52 of the ascending-HNN dossier use one mechanism over and over:
the finite residual is intrinsic, so it can be compared across an isomorphism,
and by Lemma 49.4 it is unchanged by passage to a finite-index subgroup.  Those
two facts together are what separates the alternating-lamp family up to
*commensurability* rather than merely up to isomorphism.

* `finiteResidual_eq_subgroupOf` — the subgroup form of Lemma 49.4: for a
  finite-index subgroup the finite residual is literally the trace of the
  ambient one.
* `map_finiteResidual_eq` and `mulEquivFiniteResidual` — an isomorphism of
  groups carries the finite residual onto the finite residual, so the residuals
  are isomorphic.
* `not_mulEquiv_of_finiteResidual_not_mulEquiv` and the finite-index version
  `not_commensurable_of_finiteResidual_not_mulEquiv` — the separation criterion
  in the form the application uses: it is enough to distinguish the residuals.

Nothing here knows what the residual of any particular group is; that is the
job of the radical computation.  This file is the transport.
-/

namespace GroupApproximation

universe u v

variable {G : Type u} [Group G] {H : Type v} [Group H]

/-! ## Finite index does not change the residual -/

/-- **Lemma 49.4, subgroup form.**  For a finite-index subgroup the finite
residual is exactly the trace of the ambient finite residual. -/
theorem finiteResidual_eq_subgroupOf {K : Subgroup G} [K.FiniteIndex] :
    finiteResidual K = (finiteResidual G).subgroupOf K := by
  ext x
  rw [Subgroup.mem_subgroupOf]
  exact mem_finiteResidual_subgroup_iff x

/-! ## Isomorphisms carry the residual onto the residual -/

/-- An isomorphism maps the finite residual onto the finite residual. -/
theorem map_finiteResidual_eq (e : G ≃* H) :
    (finiteResidual G).map e.toMonoidHom = finiteResidual H := by
  refine le_antisymm (map_finiteResidual_le e.toMonoidHom) ?_
  rw [SetLike.le_def]
  intro y hy
  refine ⟨e.symm y, ?_, by simp⟩
  have hmap := map_finiteResidual_le e.symm.toMonoidHom (x := e.symm y)
  exact hmap ⟨y, hy, rfl⟩

/-- The finite residuals of isomorphic groups are isomorphic. -/
noncomputable def mulEquivFiniteResidual (e : G ≃* H) :
    finiteResidual G ≃* finiteResidual H :=
  (MulEquiv.subgroupMap e (finiteResidual G)).trans
    (MulEquiv.subgroupCongr (map_finiteResidual_eq e))

/-! ## The separation criterion -/

/-- If the finite residuals are not isomorphic, neither are the groups. -/
theorem not_mulEquiv_of_finiteResidual_not_mulEquiv
    (h : IsEmpty (finiteResidual G ≃* finiteResidual H)) :
    IsEmpty (G ≃* H) := by
  refine ⟨fun e => ?_⟩
  exact h.elim (mulEquivFiniteResidual e)

/-- **The commensurability criterion.**  If the finite residual of every
finite-index subgroup of `G` is `R_G`, and likewise for `H`, and `R_G` is not
isomorphic to `R_H`, then no finite-index subgroup of `G` is isomorphic to a
finite-index subgroup of `H`.

Stated in the form the alternating-lamp family uses: the hypothesis is that the
two ambient residuals are already pinned, and Lemma 49.4 transports them down. -/
theorem not_commensurable_of_finiteResidual_not_mulEquiv
    {K : Subgroup G} [K.FiniteIndex] {L : Subgroup H} [L.FiniteIndex]
    (h : IsEmpty ((finiteResidual G).subgroupOf K
      ≃* (finiteResidual H).subgroupOf L)) :
    IsEmpty (K ≃* L) := by
  refine ⟨fun e => ?_⟩
  have hK : finiteResidual K = (finiteResidual G).subgroupOf K :=
    finiteResidual_eq_subgroupOf
  have hL : finiteResidual L = (finiteResidual H).subgroupOf L :=
    finiteResidual_eq_subgroupOf
  refine h.elim ?_
  exact ((MulEquiv.subgroupCongr hK).symm.trans
    (mulEquivFiniteResidual e)).trans (MulEquiv.subgroupCongr hL)

end GroupApproximation
