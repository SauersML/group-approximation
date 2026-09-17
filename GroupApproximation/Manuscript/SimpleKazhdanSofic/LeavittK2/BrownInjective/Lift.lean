import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.Presentation
import GroupApproximation.Meta.AxiomGuard

/-!
# Brown presentation II: lifting single edge steps (lane sk-leavitt-12)

Khanh, tex l.460: "Starting at a vertex represented by a transporter $g$, it is encoded by a
word $jT$ [...]. Two choices describing the same ordered edge differ by its stabilizer $K$,
and the first relations identify them. At the endpoint, the difference from a prescribed
transporter is again in $J$. [...] Backtracking cancels inverse words, and a passage across
a triangle is a translate of the relation just computed."

A transporter `x : Π` sits at `p(x) v₀`.  `Step x y` means `y = x·g·T·j` with `g, j ∈ J`,
so `p(y) v₀ = p(x) g v₁`.  We prove: steps exist along every edge (`step_exists`), are unique
up to right `J`-cosets (`step_unique`), backtracking returns to the coset (`step_back`), and
two routes around an ordered triangle agree up to `J` (`step_tri`).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective

universe u v

variable {G : Type u} {V : Type v} [Group G] [MulAction G V]

namespace BrownSetting

variable (S : BrownSetting G V)

theorem J_smul_v0 (j : S.J) : (j : G) • S.v0 = S.v0 := MulAction.mem_stabilizer_iff.mp j.2

theorem coe_hJ : (S.hJ : G) = S.h := rfl

/-- `x` and `y` lie in the same right coset `x J`. -/
def SameCoset (x y : S.PiGroup) : Prop := ∃ j : S.J, y = x * S.incl j

theorem sameCoset_refl (x : S.PiGroup) : S.SameCoset x x := ⟨1, by rw [map_one, mul_one]⟩

theorem sameCoset_symm {x y : S.PiGroup} (h : S.SameCoset x y) : S.SameCoset y x := by
  obtain ⟨j, rfl⟩ := h
  exact ⟨j⁻¹, by rw [map_inv, mul_inv_cancel_right]⟩

theorem sameCoset_trans {x y z : S.PiGroup} (h1 : S.SameCoset x y) (h2 : S.SameCoset y z) :
    S.SameCoset x z := by
  obtain ⟨j1, rfl⟩ := h1
  obtain ⟨j2, rfl⟩ := h2
  exact ⟨j1 * j2, by rw [map_mul, mul_assoc]⟩

theorem sameCoset_v0 {x y : S.PiGroup} (h : S.SameCoset x y) :
    S.p y • S.v0 = S.p x • S.v0 := by
  obtain ⟨j, rfl⟩ := h
  rw [map_mul, S.p_incl, mul_smul, S.J_smul_v0]

/-- One edge step from the transporter `x`. -/
def Step (x y : S.PiGroup) : Prop := ∃ g j : S.J, y = x * S.incl g * S.T * S.incl j

theorem p_step_v0 (x : S.PiGroup) (g j : S.J) :
    S.p (x * S.incl g * S.T * S.incl j) • S.v0 = S.p x • ((g : G) • S.v1) := by
  simp only [map_mul, S.p_incl, S.p_T, mul_smul, S.J_smul_v0, S.tau_v0]

theorem step_edge {x y : S.PiGroup} (hs : S.Step x y) :
    S.edge (S.p x • S.v0) (S.p y • S.v0) := by
  obtain ⟨g, j, rfl⟩ := hs
  rw [S.p_step_v0]
  have h := S.edge_smul (S.p x * (g : G)) _ _ S.edge_base
  rwa [mul_smul, S.J_smul_v0, mul_smul] at h

theorem step_exists (x : S.PiGroup) (w : V) (he : S.edge (S.p x • S.v0) w) :
    ∃ y, S.Step x y ∧ S.p y • S.v0 = w := by
  have he' : S.edge S.v0 ((S.p x)⁻¹ • w) := by
    have h := S.edge_smul (S.p x)⁻¹ _ _ he
    rwa [inv_smul_smul] at h
  obtain ⟨g, hg0, hg1⟩ := S.edge_transitive _ _ he'
  refine ⟨x * S.incl ⟨g, MulAction.mem_stabilizer_iff.mpr hg0⟩ * S.T * S.incl 1,
    ⟨_, 1, rfl⟩, ?_⟩
  rw [S.p_step_v0]
  show S.p x • (g • S.v1) = w
  rw [hg1, smul_inv_smul]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.step_exists

/-- `T k T = k'` for `k ∈ K`: the relation `T k T⁻¹ = τ k τ⁻¹` together with `T² = 1`. -/
theorem T_conj_T (k : S.J) (hk : (k : G) • S.v1 = S.v1) :
    ∃ k' : S.J, S.T * S.incl k * S.T = S.incl k' := by
  have hv0 : (S.tau⁻¹ * k * S.tau) • S.v0 = S.v0 := by
    rw [mul_smul, mul_smul, S.tau_v0, hk, ← S.tau_v0, inv_smul_smul]
  have hv1 : (S.tau⁻¹ * k * S.tau) • S.v1 = S.v1 := by
    rw [mul_smul, mul_smul, S.tau_v1, S.J_smul_v0, ← S.tau_v1, inv_smul_smul]
  obtain ⟨k', hk'⟩ : ∃ k' : S.J, (k' : G) = S.tau⁻¹ * k * S.tau :=
    ⟨⟨S.tau⁻¹ * k * S.tau, MulAction.mem_stabilizer_iff.mpr hv0⟩, rfl⟩
  have hb : (k : G) = S.tau * (k' : G) * S.tau⁻¹ := by
    rw [hk']
    simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
  have h := S.rel_conj k' k (by rw [hk']; exact hv1) hb
  refine ⟨k', ?_⟩
  rw [← h, S.T_inv]
  simp only [mul_assoc, S.T_mul_T_left, S.T_mul_T, mul_one]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.T_conj_T

/-- Uniqueness of steps up to `J` (the `K`-ambiguity of an edge choice). -/
theorem step_unique {x x' y y' : S.PiGroup} (hs : S.Step x y) (hs' : S.Step x' y')
    (hx : S.SameCoset x x') (hv : S.p y • S.v0 = S.p y' • S.v0) : S.SameCoset y y' := by
  obtain ⟨g, j, rfl⟩ := hs
  obtain ⟨g', j', rfl⟩ := hs'
  obtain ⟨j0, rfl⟩ := hx
  rw [S.p_step_v0, S.p_step_v0, map_mul, S.p_incl, mul_smul, smul_left_cancel_iff] at hv
  have hk : ((g⁻¹ * j0 * g' : S.J) : G) • S.v1 = S.v1 := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, mul_smul, ← hv,
      inv_smul_smul]
  obtain ⟨k', hk'⟩ := S.T_conj_T (g⁻¹ * j0 * g') hk
  refine ⟨j⁻¹ * k' * j', ?_⟩
  simp only [map_mul, map_inv]
  rw [← hk']
  simp only [map_mul, map_inv, mul_assoc, mul_inv_cancel_left, S.T_mul_T_left]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.BrownSetting.step_unique

end BrownSetting

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective
