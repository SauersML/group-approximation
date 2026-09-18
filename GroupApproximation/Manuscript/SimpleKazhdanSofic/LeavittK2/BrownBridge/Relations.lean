import Mathlib.GroupTheory.PresentedGroup
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.Swaps
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Frame.Base
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.Presentation
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CriterionInterfaces
import GroupApproximation.Meta.AxiomGuard

/-!
# Brown bridge IV: lane 14's relations present a map out of Brown's group (lane sk-leavitt-20)

`frameSetting := frameBrownSetting L 1` is lane 12's `BrownSetting` for `GL₄(L)` on the frame
vertices `X₄(L)`, with `v₀ = e₃`, `v₁ = e₂`, `τ = frameTau L 2`, `h = frameHSwap L 1`.

Route.
* `mem_vertexStab_of_mem_J`, `mem_J_of_mem_vertexStab`: lane 12's `J = Stab(v₀)` is lane 14's
  `vertexStab` (both say `g e₃ = e₃`), and `jHom : J →* vertexStab` is the inclusion.
* `bridge_rels`: for `f : vertexStab →* St₄(L)` and `t` with `EdgeRelation f t` and
  `TriangleRelation f t`, the generator map `j ↦ f j`, `T ↦ t` kills every relator of `Π`:
  the multiplication relators because `f` is a homomorphism; the conjugation relators by
  `EdgeRelation`, as `a v₁ = v₁` is `a e₂ = e₂` and `τ = swapLast` (`swapLast_eq_frameTau`);
  the braid relator by `TriangleRelation`, as `h = swapMid` (`swapMid_eq_frameHSwap`).
* `bridgeLift : Π →* St₄(L)` with `bridgeLift_incl` and `bridgeLift_T`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge

open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Criterion
open GroupApproximation.BooneHigman.SteinbergBasic
open scoped Matrix

noncomputable section

/-- Lane 12's Brown setting for `GL₄(L)` acting on the frame complex `X₄(L)`. -/
abbrev frameSetting : BrownSetting GLFour (FrameVertices BinL 4) :=
  frameBrownSetting BinL 1

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.frameSetting

theorem mem_vertexStab_of_mem_J {g : GLFour} (hg : g ∈ frameSetting.J) : g ∈ vertexStab := by
  have h := congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp hg)
  show (g : Matrix (Fin 4) (Fin 4) BinL) *ᵥ lastCol = lastCol
  exact h

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.mem_vertexStab_of_mem_J

theorem mem_J_of_mem_vertexStab {g : GLFour} (hg : g ∈ vertexStab) : g ∈ frameSetting.J := by
  have h : (g : Matrix (Fin 4) (Fin 4) BinL) *ᵥ lastCol = lastCol := hg
  exact MulAction.mem_stabilizer_iff.mpr (Subtype.ext h)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.mem_J_of_mem_vertexStab

theorem J_le_vertexStab : frameSetting.J ≤ vertexStab :=
  fun _ hg => mem_vertexStab_of_mem_J hg

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.J_le_vertexStab

/-- The inclusion of lane 12's `J` into lane 14's `vertexStab`. -/
abbrev jHom : frameSetting.J →* vertexStab :=
  Subgroup.inclusion J_le_vertexStab

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.jHom

theorem jHom_mk (j : vertexStab) : jHom ⟨j, mem_J_of_mem_vertexStab j.2⟩ = j :=
  Subtype.ext rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.jHom_mk

/-- The generator map `j ↦ f j`, `T ↦ t`. -/
def bridgeGen (f : vertexStab →* St 4 BinL) (t : St 4 BinL) :
    frameSetting.J ⊕ Unit → St 4 BinL :=
  Sum.elim (fun a => f (jHom a)) (fun _ => t)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.bridgeGen

/-- Lane 14's edge and triangle relations kill every relator of Brown's group `Π`. -/
theorem bridge_rels (f : vertexStab →* St 4 BinL) (t : St 4 BinL) (hE : EdgeRelation f t)
    (hT : TriangleRelation f t) :
    ∀ r ∈ frameSetting.rels, FreeGroup.lift (bridgeGen f t) r = 1 := by
  intro r hr
  simp only [BrownSetting.rels, Set.mem_union, Set.mem_setOf_eq] at hr
  rcases hr with ⟨a, b, rfl⟩ | ⟨a, b, ha, hb, rfl⟩ | rfl
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of, bridgeGen, Sum.elim_inl]
    exact mul_inv_cancel _
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of, bridgeGen, Sum.elim_inl, Sum.elim_inr]
    have hprev := congrArg Subtype.val ha
    have hconj : ((jHom b : vertexStab) : GLFour) =
        swapLast * ((jHom a : vertexStab) : GLFour) * swapLast⁻¹ := by
      rw [swapLast_eq_frameTau]
      exact hb
    exact mul_inv_eq_one.mpr (hE (jHom a) (jHom b) hprev hconj)
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of, bridgeGen, Sum.elim_inl, Sum.elim_inr]
    exact mul_inv_eq_one.mpr (hT (jHom frameSetting.hJ) swapMid_eq_frameHSwap.symm)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.bridge_rels

/-- The homomorphism `Π →* St₄(L)` presented by `j ↦ f j`, `T ↦ t`. -/
def bridgeLift (f : vertexStab →* St 4 BinL) (t : St 4 BinL) (hE : EdgeRelation f t)
    (hT : TriangleRelation f t) : frameSetting.PiGroup →* St 4 BinL :=
  PresentedGroup.toGroup (bridge_rels f t hE hT)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.bridgeLift

theorem bridgeLift_incl (f : vertexStab →* St 4 BinL) (t : St 4 BinL) (hE : EdgeRelation f t)
    (hT : TriangleRelation f t) (a : frameSetting.J) :
    bridgeLift f t hE hT (frameSetting.incl a) = f (jHom a) := by
  rw [BrownSetting.incl_apply]
  exact PresentedGroup.toGroup.of (bridge_rels f t hE hT)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.bridgeLift_incl

theorem bridgeLift_T (f : vertexStab →* St 4 BinL) (t : St 4 BinL) (hE : EdgeRelation f t)
    (hT : TriangleRelation f t) : bridgeLift f t hE hT frameSetting.T = t :=
  PresentedGroup.toGroup.of (bridge_rels f t hE hT)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.bridgeLift_T

end

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge
