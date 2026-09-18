import Mathlib.GroupTheory.Finiteness
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2OneVarTransport
import GroupApproximation.Meta.AxiomGuard

/-!
# Telescope for the nil part of `K₂`: two kernel lemmas

Lane `bh-met-95b`, core module.  Pure group theory on top of the functoriality of `K₂(I, -)`
(`ElemFP.K2Map_K2Map`, `ElemFP.K2Map_K2Map_of_comp_eq_id`).  No hypothesis on the rings.

* `subgroup_fg_map`: the image of a finitely generated subgroup is finitely generated.
* `ker_K2Map_eq_map_sup_ker` (**the split**): let `p : R → R'` be a ring map with a section
  `s`, and let `c = c' ∘ p`.  Then
  `ker (K₂ c) = s_*(ker (K₂ c')) ⊔ ker (K₂ p)`.
  Every `u ∈ ker (K₂ c)` is `s_*(p_* u) · ((s_*(p_* u))⁻¹ u)`, the first factor in the image of
  `ker (K₂ c')`, the second killed by `p_*`.  Both pieces lie in `ker (K₂ c)`.
* `fg_ker_K2Map_of_split`: so `ker (K₂ c)` is finitely generated once `ker (K₂ c')` and
  `ker (K₂ p)` are.  This is one step of the telescope: `ker (K₂ p)` is the graded piece.
* `ker_K2Map_eq_map_of_retract`, `fg_ker_K2Map_of_retract`: if `P ∘ Q = id` and the two
  squares `κ₁ ∘ P = P' ∘ κ₂`, `κ₂ ∘ Q = Q' ∘ κ₁` commute, then `ker (K₂ κ₁)` is the image of
  `ker (K₂ κ₂)` under `P_*`, hence finitely generated when `ker (K₂ κ₂)` is.  This is used to
  change the base ring of a graded piece (adding dummy variables) and to transport along
  `MvPolynomial.finSuccEquiv`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPNilFGPosTele

open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.BooneHigman.Metabelian.ElemFP

section Map

variable {G G' : Type*} [Group G] [Group G']

/-- The image of a finitely generated subgroup under a homomorphism is finitely generated. -/
theorem subgroup_fg_map (f : G →* G') {H : Subgroup G} (h : H.FG) : (H.map f).FG := by
  obtain ⟨S, hS, hfin⟩ := (Subgroup.fg_iff H).mp h
  exact (Subgroup.fg_iff _).mpr ⟨f '' S, by rw [← MonoidHom.map_closure, hS], hfin.image f⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPNilFGPosTele.subgroup_fg_map

end Map

section Split

variable {I R R' Z : Type*} [Fintype I] [DecidableEq I] [Ring R] [Ring R'] [Ring Z]

/-- **The split.**  If `p ∘ s = id` and `c = c' ∘ p`, then
`ker (K₂ c) = s_*(ker (K₂ c')) ⊔ ker (K₂ p)`. -/
theorem ker_K2Map_eq_map_sup_ker (p : R →+* R') (s : R' →+* R)
    (hps : p.comp s = RingHom.id R') (c : R →+* Z) (c' : R' →+* Z) (hc : c'.comp p = c) :
    (K2Map (I := I) c).ker =
      (K2Map (I := I) c').ker.map (K2Map (I := I) s) ⊔ (K2Map (I := I) p).ker := by
  have hcs : c.comp s = c' := by
    rw [← hc, RingHom.comp_assoc, hps, RingHom.comp_id]
  refine le_antisymm (fun u hu ↦ ?_) (sup_le ?_ ?_)
  · have hv : K2Map (I := I) p u ∈ (K2Map (I := I) c').ker := by
      rw [MonoidHom.mem_ker, K2Map_K2Map, hc]
      exact MonoidHom.mem_ker.mp hu
    have hw : (K2Map (I := I) s (K2Map (I := I) p u))⁻¹ * u ∈ (K2Map (I := I) p).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, K2Map_K2Map_of_comp_eq_id p s hps,
        inv_mul_cancel]
    have hmem := Subgroup.mul_mem_sup (Subgroup.mem_map_of_mem (K2Map (I := I) s) hv) hw
    rwa [mul_inv_cancel_left] at hmem
  · intro x hx
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
    rw [MonoidHom.mem_ker, K2Map_K2Map, hcs]
    exact MonoidHom.mem_ker.mp hw
  · intro w hw
    rw [MonoidHom.mem_ker, ← hc, ← K2Map_K2Map, MonoidHom.mem_ker.mp hw, map_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPNilFGPosTele.ker_K2Map_eq_map_sup_ker

/-- **One telescope step.**  If `p ∘ s = id` and `c = c' ∘ p`, then `ker (K₂ c)` is finitely
generated once `ker (K₂ c')` and the graded piece `ker (K₂ p)` are. -/
theorem fg_ker_K2Map_of_split (p : R →+* R') (s : R' →+* R)
    (hps : p.comp s = RingHom.id R') (c : R →+* Z) (c' : R' →+* Z) (hc : c'.comp p = c)
    (h' : Group.FG (K2Map (I := I) c').ker) (hp : Group.FG (K2Map (I := I) p).ker) :
    Group.FG (K2Map (I := I) c).ker := by
  rw [Group.fg_iff_subgroup_fg] at h' hp ⊢
  rw [ker_K2Map_eq_map_sup_ker p s hps c c' hc]
  exact (subgroup_fg_map _ h').sup hp

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPNilFGPosTele.fg_ker_K2Map_of_split

end Split

section Retract

variable {I R₁ R₂ S₁ S₂ : Type*} [Fintype I] [DecidableEq I] [Ring R₁] [Ring R₂] [Ring S₁]
  [Ring S₂]

/-- **Retract of a kernel.**  If `P ∘ Q = id`, `κ₁ ∘ P = P' ∘ κ₂` and `κ₂ ∘ Q = Q' ∘ κ₁`, then
`ker (K₂ κ₁)` is the image of `ker (K₂ κ₂)` under `P_*`. -/
theorem ker_K2Map_eq_map_of_retract (κ₁ : R₁ →+* S₁) (κ₂ : R₂ →+* S₂) (P : R₂ →+* R₁)
    (Q : R₁ →+* R₂) (P' : S₂ →+* S₁) (Q' : S₁ →+* S₂) (hPQ : P.comp Q = RingHom.id R₁)
    (hP : κ₁.comp P = P'.comp κ₂) (hQ : κ₂.comp Q = Q'.comp κ₁) :
    (K2Map (I := I) κ₁).ker = (K2Map (I := I) κ₂).ker.map (K2Map (I := I) P) := by
  refine le_antisymm (fun u hu ↦ ?_) (fun x hx ↦ ?_)
  · refine Subgroup.mem_map.mpr
      ⟨K2Map (I := I) Q u, ?_, K2Map_K2Map_of_comp_eq_id P Q hPQ u⟩
    rw [MonoidHom.mem_ker, K2Map_K2Map, hQ, ← K2Map_K2Map, MonoidHom.mem_ker.mp hu, map_one]
  · obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
    rw [MonoidHom.mem_ker, K2Map_K2Map, hP, ← K2Map_K2Map, MonoidHom.mem_ker.mp hw, map_one]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPNilFGPosTele.ker_K2Map_eq_map_of_retract

/-- Finite generation passes to a retract of a kernel (hypotheses as in
`ker_K2Map_eq_map_of_retract`). -/
theorem fg_ker_K2Map_of_retract (κ₁ : R₁ →+* S₁) (κ₂ : R₂ →+* S₂) (P : R₂ →+* R₁)
    (Q : R₁ →+* R₂) (P' : S₂ →+* S₁) (Q' : S₁ →+* S₂) (hPQ : P.comp Q = RingHom.id R₁)
    (hP : κ₁.comp P = P'.comp κ₂) (hQ : κ₂.comp Q = Q'.comp κ₁)
    (h : Group.FG (K2Map (I := I) κ₂).ker) : Group.FG (K2Map (I := I) κ₁).ker := by
  rw [Group.fg_iff_subgroup_fg] at h ⊢
  rw [ker_K2Map_eq_map_of_retract κ₁ κ₂ P Q P' Q' hPQ hP hQ]
  exact subgroup_fg_map _ h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPNilFGPosTele.fg_ker_K2Map_of_retract

end Retract

end GroupApproximation.BooneHigman.Metabelian.ElemFPNilFGPosTele
