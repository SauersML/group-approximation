import Mathlib.GroupTheory.PresentedGroup
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.Setting
import GroupApproximation.Meta.AxiomGuard

/-!
# Brown presentation II: the group `Π` and the projection `p` (lane sk-leavitt-12)

Khanh, proof of the Steinberg comparison criterion (tex l.452):
$$\Pi=\langle J,T\mid TkT^{-1}=\eta(k)\text{ for }k\in K,\quad ThT=hTh\rangle,$$
"This notation includes every multiplication relation in $J$", and
"the projection $p:\Pi\to G$, given by $p(j)=j$ and $p(T)=\tau$".

Here `J = Stab(v₀)`, `K = Stab(v₀) ∩ Stab(v₁)` and `η(k) = τ k τ⁻¹`.  The conjugation
relation is imposed in the form: for `a, b ∈ J` with `a v₁ = v₁` and `b = τ a τ⁻¹`,
`T a T⁻¹ = b`.  We derive `T² = 1` (tex l.460).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective

universe u v

variable {G : Type u} {V : Type v} [Group G] [MulAction G V]

/-- In any group, `e² = 1` and `t e t = e t e` imply `t² = 1`. -/
theorem sq_one_of_braid {Γ : Type*} [Group Γ] (t e : Γ) (hη : e * e = 1)
    (hb : t * e * t = e * t * e) : t * t = 1 := by
  have hA : e * t * e * t * e = t := by
    calc e * t * e * t * e = e * (t * e * t) * e := by simp only [mul_assoc]
      _ = e * (e * t * e) * e := by rw [hb]
      _ = (e * e) * t * (e * e) := by simp only [mul_assoc]
      _ = t := by rw [hη, one_mul, mul_one]
  have hB : e * t * e * t⁻¹ * e = t := by
    calc e * t * e * t⁻¹ * e = (e * t * e) * t⁻¹ * e := rfl
      _ = (t * e * t) * t⁻¹ * e := by rw [← hb]
      _ = t * (e * e) := by simp only [mul_assoc, mul_inv_cancel_left]
      _ = t := by rw [hη, mul_one]
  have hC : e * t * e * t * e = e * t * e * t⁻¹ * e := hA.trans hB.symm
  have hD : t = t⁻¹ := mul_left_cancel (mul_right_cancel hC)
  exact mul_eq_one_iff_eq_inv.mpr hD

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.sq_one_of_braid

namespace BrownSetting

variable (S : BrownSetting G V)

/-- The vertex stabilizer `J = Stab(v₀)`. -/
abbrev J : Subgroup G := MulAction.stabilizer G S.v0

/-- `h` as an element of `J`. -/
def hJ : S.J := ⟨S.h, MulAction.mem_stabilizer_iff.mpr S.h_v0⟩

/-- The defining relations of `Π`, over the generators `J ⊔ {T}`. -/
def rels : Set (FreeGroup (S.J ⊕ Unit)) :=
  {r | ∃ a b : S.J, r = FreeGroup.of (Sum.inl a) * FreeGroup.of (Sum.inl b) *
      (FreeGroup.of (Sum.inl (a * b)))⁻¹} ∪
  ({r | ∃ a b : S.J, (a : G) • S.v1 = S.v1 ∧ (b : G) = S.tau * a * S.tau⁻¹ ∧
      r = FreeGroup.of (Sum.inr ()) * FreeGroup.of (Sum.inl a) * (FreeGroup.of (Sum.inr ()))⁻¹ *
        (FreeGroup.of (Sum.inl b))⁻¹} ∪
    {r | r = FreeGroup.of (Sum.inr ()) * FreeGroup.of (Sum.inl S.hJ) * FreeGroup.of (Sum.inr ()) *
      (FreeGroup.of (Sum.inl S.hJ) * FreeGroup.of (Sum.inr ()) * FreeGroup.of (Sum.inl S.hJ))⁻¹})

/-- Brown's group `Π = ⟨J, T | ...⟩`. -/
abbrev PiGroup : Type u := PresentedGroup S.rels

/-- The generator images in `G`: `j ↦ j`, `T ↦ τ`. -/
def genMap : S.J ⊕ Unit → G := Sum.elim (fun a => (a : G)) (fun _ => S.tau)

theorem lift_rels : ∀ r ∈ S.rels, FreeGroup.lift S.genMap r = 1 := by
  intro r hr
  simp only [rels, Set.mem_union, Set.mem_setOf_eq] at hr
  rcases hr with ⟨a, b, rfl⟩ | ⟨a, b, -, hb, rfl⟩ | rfl
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of, genMap, Sum.elim_inl,
      Subgroup.coe_mul]
    exact mul_inv_cancel _
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of, genMap, Sum.elim_inl, Sum.elim_inr,
      hb]
    exact mul_inv_cancel _
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of, genMap, Sum.elim_inl, Sum.elim_inr]
    exact mul_inv_eq_one.mpr S.braid

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.lift_rels

/-- The projection `p : Π → G` (`brownMap`). -/
def p : S.PiGroup →* G := PresentedGroup.toGroup S.lift_rels

theorem mem_rels_mul (a b : S.J) :
    FreeGroup.of (Sum.inl a) * FreeGroup.of (Sum.inl b) * (FreeGroup.of (Sum.inl (a * b)))⁻¹
      ∈ S.rels := by
  exact Or.inl ⟨a, b, rfl⟩

theorem mem_rels_conj (a b : S.J) (ha : (a : G) • S.v1 = S.v1)
    (hb : (b : G) = S.tau * a * S.tau⁻¹) :
    FreeGroup.of (Sum.inr ()) * FreeGroup.of (Sum.inl a) * (FreeGroup.of (Sum.inr ()))⁻¹ *
      (FreeGroup.of (Sum.inl b))⁻¹ ∈ S.rels := by
  exact Or.inr (Or.inl ⟨a, b, ha, hb, rfl⟩)

theorem mem_rels_braid :
    FreeGroup.of (Sum.inr ()) * FreeGroup.of (Sum.inl S.hJ) * FreeGroup.of (Sum.inr ()) *
      (FreeGroup.of (Sum.inl S.hJ) * FreeGroup.of (Sum.inr ()) * FreeGroup.of (Sum.inl S.hJ))⁻¹
      ∈ S.rels := by
  exact Or.inr (Or.inr rfl)

theorem of_inl_mul (a b : S.J) :
    (PresentedGroup.of (Sum.inl (a * b)) : S.PiGroup) =
      PresentedGroup.of (Sum.inl a) * PresentedGroup.of (Sum.inl b) := by
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem (S.mem_rels_mul a b)
  rw [map_mul] at h
  exact h.symm

/-- The inclusion `J → Π`. -/
def incl : S.J →* S.PiGroup :=
  MonoidHom.mk' (fun a => PresentedGroup.of (Sum.inl a)) S.of_inl_mul

/-- The generator `T`. -/
def T : S.PiGroup := PresentedGroup.of (Sum.inr ())

theorem incl_apply (a : S.J) : S.incl a = PresentedGroup.of (Sum.inl a) := rfl

theorem p_incl (a : S.J) : S.p (S.incl a) = (a : G) := by
  rw [incl_apply]
  exact PresentedGroup.toGroup.of S.lift_rels

theorem p_T : S.p S.T = S.tau := PresentedGroup.toGroup.of S.lift_rels

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.p_incl
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.p_T

/-- The relation `T a T⁻¹ = τ a τ⁻¹` for `a ∈ K`. -/
theorem rel_conj (a b : S.J) (ha : (a : G) • S.v1 = S.v1)
    (hb : (b : G) = S.tau * a * S.tau⁻¹) :
    S.T * S.incl a * S.T⁻¹ = S.incl b := by
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem (S.mem_rels_conj a b ha hb)
  simp only [map_mul, map_inv] at h
  exact h

/-- The braid relation `ThT = hTh` in `Π`. -/
theorem rel_braid : S.T * S.incl S.hJ * S.T = S.incl S.hJ * S.T * S.incl S.hJ := by
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem S.mem_rels_braid
  simp only [map_mul] at h
  exact h

theorem incl_hJ_mul_self : S.incl S.hJ * S.incl S.hJ = 1 := by
  have h2 : S.hJ * S.hJ = 1 := Subtype.ext S.h_mul_h
  rw [← map_mul, h2, map_one]

/-- `T² = 1` (tex l.460), derived from `h² = 1` and the braid relation. -/
theorem T_mul_T : S.T * S.T = 1 :=
  sq_one_of_braid S.T (S.incl S.hJ) S.incl_hJ_mul_self S.rel_braid

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.T_mul_T

theorem T_inv : S.T⁻¹ = S.T := (mul_eq_one_iff_eq_inv.mp S.T_mul_T).symm

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.T_inv
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.J
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.hJ
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.rels
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.PiGroup
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.genMap
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.p
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.mem_rels_mul
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.mem_rels_conj
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.mem_rels_braid
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.of_inl_mul
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.incl
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.T
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.incl_apply
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.rel_conj
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.rel_braid
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.incl_hJ_mul_self

end BrownSetting

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective
