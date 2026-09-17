import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.Homotopy
import GroupApproximation.Meta.AxiomGuard

/-!
# Brown presentation II: injectivity from simple connectivity (lane sk-leavitt-12)

Khanh, proof of the Steinberg comparison criterion (tex l.452–460): "the projection
$p:\Pi\to G$, given by $p(j)=j$ and $p(T)=\tau$, is an isomorphism", and "If $w$ lies in
the kernel, its encoded path is a closed loop [...] Thus no additional path relation is
required."

Route.  Every `x ∈ Π` is, up to right multiplication by `J`, the endpoint of a lift from `1`
of an edge path from `v₀` (`reach`, induction over free-group words: a letter `j ∈ J` stays in
the coset, a letter `T = T⁻¹` appends one step).  If `p x = 1`, that path is a loop at `v₀`;
by simple connectivity it is homotopic to the empty path, so by `homotopic_lift` the lift
endpoint lies in `J`; hence `x ∈ J`, and `p` restricted to `J` is the inclusion, so `x = 1`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective

universe u v

variable {G : Type u} {V : Type v} [Group G] [MulAction G V]

namespace BrownSetting

variable (S : BrownSetting G V)

/-- Brown's projection `Π → G` (`p(j) = j`, `p(T) = τ`). -/
abbrev brownMap : S.PiGroup →* G := S.p

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.brownMap

/-- `x` is, up to `J`, the endpoint of a lift from `1` of an edge path. -/
def Reach (x : S.PiGroup) : Prop :=
  ∃ (l : List V) (z : S.PiGroup), S.LiftEnd 1 l z ∧ S.SameCoset z x

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.Reach

theorem reach_one : S.Reach 1 := ⟨[], 1, LiftEnd.nil 1, S.sameCoset_refl 1⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.reach_one

theorem reach_mul_incl {x : S.PiGroup} (hx : S.Reach x) (j : S.J) : S.Reach (x * S.incl j) := by
  obtain ⟨l, z, hl, hz⟩ := hx
  exact ⟨l, z, hl, S.sameCoset_trans hz ⟨j, rfl⟩⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.reach_mul_incl

theorem reach_mul_T {x : S.PiGroup} (hx : S.Reach x) : S.Reach (x * S.T) := by
  obtain ⟨l, z, hl, j0, rfl⟩ := hx
  have hs : S.Step z (z * S.incl j0 * S.T) := ⟨j0, 1, by rw [map_one, mul_one]⟩
  exact ⟨l ++ [S.p (z * S.incl j0 * S.T) • S.v0], z * S.incl j0 * S.T,
    LiftEnd.append S hl (LiftEnd.cons hs rfl (LiftEnd.nil _)), S.sameCoset_refl _⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.reach_mul_T

theorem mk_of_inl (j : S.J) :
    PresentedGroup.mk S.rels (FreeGroup.of (Sum.inl j)) = S.incl j := rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.mk_of_inl

theorem mk_of_inr :
    PresentedGroup.mk S.rels (FreeGroup.of (Sum.inr ())) = S.T := rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.mk_of_inr

theorem reach_mul_mk (w : FreeGroup (S.J ⊕ Unit)) :
    ∀ x : S.PiGroup, S.Reach x → S.Reach (x * PresentedGroup.mk S.rels w) := by
  induction w using FreeGroup.induction_on with
  | C1 =>
    intro x hx
    rw [map_one, mul_one]
    exact hx
  | of a =>
    intro x hx
    rcases a with j | ⟨⟩
    · rw [S.mk_of_inl]
      exact S.reach_mul_incl hx j
    · rw [S.mk_of_inr]
      exact S.reach_mul_T hx
  | inv_of a _ =>
    intro x hx
    rcases a with j | ⟨⟩
    · rw [map_inv, S.mk_of_inl, ← map_inv]
      exact S.reach_mul_incl hx j⁻¹
    · rw [map_inv, S.mk_of_inr, S.T_inv]
      exact S.reach_mul_T hx
  | mul _ _ ha hb =>
    intro x hx
    rw [map_mul, ← mul_assoc]
    exact hb _ (ha x hx)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.reach_mul_mk

theorem reach (x : S.PiGroup) : S.Reach x := by
  induction x using PresentedGroup.induction_on with
  | H w =>
    have h := S.reach_mul_mk w 1 S.reach_one
    rwa [one_mul] at h

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.reach

/-- **Brown presentation II.**  If the complex is (combinatorially) simply connected, Brown's
projection `p : Π → G` is injective. -/
theorem brownMap_injective (hsc : S.SimplyConnected) : Function.Injective S.brownMap := by
  show Function.Injective S.p
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨l, z, hl, j, rfl⟩ := S.reach x
  have hpz : S.p z • S.v0 = S.v0 := by
    have h1 : S.p (z * S.incl j) • S.v0 = S.p z • S.v0 := S.sameCoset_v0 (x := z) (y := z * S.incl j) ⟨j, rfl⟩
    rw [← h1, hx, one_smul]
  have hp : S.IsPath S.v0 l := by
    have h := LiftEnd.isPath S hl
    rwa [map_one, one_smul] at h
  have hend : S.endpoint S.v0 l = S.v0 := by
    have h := LiftEnd.target S hl
    rw [map_one, one_smul, hpz] at h
    exact h.symm
  have hh : Relation.EqvGen (S.Move S.v0) l [] := hsc S.v0 l hp hend
  obtain ⟨j', hj'⟩ := (S.homotopic_lift hh).2 1 z 1 (by rw [map_one, one_smul]) hl
    (LiftEnd.nil 1)
  have hz : z = S.incl j'⁻¹ := by
    rw [map_inv]
    exact mul_eq_one_iff_eq_inv.mp hj'.symm
  rw [hz, ← map_mul] at hx ⊢
  rw [S.p_incl] at hx
  have hj1 : j'⁻¹ * j = 1 := Subtype.ext hx
  rw [hj1, map_one]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.brownMap_injective

end BrownSetting

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective
