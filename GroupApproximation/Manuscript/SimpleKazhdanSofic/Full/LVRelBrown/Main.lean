import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVRelBrown.Relations
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVAssembly.FrameSwaps
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVBrown.BrownLift
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFrame.Main

/-!
# The relative rank-four Brown criterion

This file proves the relative rank-four Brown criterion (Khanh, arXiv:2609.08428, Thm 5.1), which
is used on the Leavitt route to `simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`).

Let `L = L_{𝔽₂}(1,2)`, and let `Ψ : St_4(L) →* Q` kill `castSuccStab (K₂(3, L))`. Then `Ψ` kills
`K₂(4, L)` (`map_ker_eq_one_of_stab`).

Proof. First replace `Q` by `St_4(L) ⧸ ker Ψ`, which lives in `Type`. `GL_4(L)` acts on the simply
connected frame complex (`LVFrame.frameComplexFour_simplyConnected`), transitively on edges and
triangles (`LVAssembly.FrameAction`). The relative vertex section `σ = relSection Ψ hΨ : J →* Q`
and `t = Ψ (w₃₂)` satisfy Brown's edge, square and triangle relations (`LVRelBrown.Relations`).
Brown's criterion (`LVBrown.brown_lift`) extends `σ` to `F : GL_4(L) →* Q` with `F τ = t`. The
relative retraction gives `F ∘ projection = Ψ`, so `Ψ k = F 1 = 1` when `projection k = 1`.
-/

namespace GroupApproximation
namespace Full
namespace LVRelBrown

open SteinbergGroup LVAssembly LVFrame

noncomputable section

/-- The stabilizer of `e₃` in the frame action is contained in `J`. -/
theorem frameStab_le_vertexStab :
    MulAction.stabilizer GLFour baseVertex ≤ vertexStab :=
  stabilizer_eq_vertexStab.le

/-- `J` fixes the base vertex `e₃`. -/
theorem vertexStab_le_frameStab :
    vertexStab ≤ MulAction.stabilizer GLFour baseVertex :=
  stabilizer_eq_vertexStab.ge

/-- **Relative Brown criterion, `Type`-valued form** (Khanh, Thm 5.1; tex l.733-735). -/
theorem map_ker_eq_one_of_stab_type {Q : Type} [Group Q] (Ψ : SteinbergGroup (Fin 4) BinL →* Q)
    (hΨ : ∀ k : SteinbergGroup (Fin 3) BinL, projection k = 1 →
      Ψ (LVCentral.castSuccStab 3 BinL k) = 1) :
    ∀ k : SteinbergGroup (Fin 4) BinL, projection k = 1 → Ψ k = 1 := by
  intro k hk
  have hσ : RelLiftsRoots Ψ (relSection Ψ hΨ) := relSection_relLiftsRoots Ψ hΨ
  have hτ2 : (swapLast * swapLast) • baseVertex = baseVertex := by
    rw [swapLast_mul_swapLast, one_smul]
  have hh0 : swapMid ∈ MulAction.stabilizer GLFour baseVertex :=
    MulAction.mem_stabilizer_iff.mpr swapMid_smul_base
  obtain ⟨F, hFJ, hFτ⟩ := LVBrown.brown_lift (frameComplexFour BinL) frameAction
    frameComplexFour_simplyConnected baseVertex nextVertex baseEdge frame_edge_transitive
    swapLast swapMid swapLast_smul_base swapLast_smul_next swapMid_smul_base swapMid_mul_self
    swap_braid frame_tri_transitive closure_stabilizer_swapLast
    ((relSection Ψ hΨ).comp (Subgroup.inclusion frameStab_le_vertexStab)) (Ψ weylLast)
    (fun a b ha hb => relEdgeRelation Ψ (relSection Ψ hΨ) hσ
      (Subgroup.inclusion frameStab_le_vertexStab a)
      (Subgroup.inclusion frameStab_le_vertexStab b)
      (by have h := congrArg Subtype.val ha; rw [smul_val] at h; exact h) hb)
    hτ2
    (relSquare Ψ (relSection Ψ hΨ)
      (frameStab_le_vertexStab (MulAction.mem_stabilizer_iff.mpr hτ2)))
    (relTriangleRelation Ψ (relSection Ψ hΨ) hσ
      (Subgroup.inclusion frameStab_le_vertexStab ⟨swapMid, hh0⟩) rfl)
  have hret := relLift_projection_eq Ψ (relSection Ψ hΨ) F hσ
    (fun j => hFJ ⟨(j : GLFour), vertexStab_le_frameStab j.2⟩) hFτ k
  rw [hk, Subgroup.coe_one, map_one] at hret
  exact hret.symm

/-- **The relative rank-four Brown criterion** (Khanh, arXiv:2609.08428, Thm 5.1;
`simple_kazhdan_sofic_group.tex` l.733-735, `sec:questions`). A homomorphism
`Ψ : St_4(L) →* Q` that kills `castSuccStab (K₂(3, L))` kills `K₂(4, L)`. -/
theorem map_ker_eq_one_of_stab {Q : Type*} [Group Q]
    (Ψ : GroupApproximation.SteinbergGroup (Fin 4)
      (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) →* Q)
    (hΨ : ∀ k : GroupApproximation.SteinbergGroup (Fin 3)
        (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)),
      GroupApproximation.SteinbergGroup.projection k = 1 →
        Ψ (GroupApproximation.Full.LVCentral.castSuccStab 3
          (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) k) = 1) :
    ∀ k : GroupApproximation.SteinbergGroup (Fin 4)
        (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)),
      GroupApproximation.SteinbergGroup.projection k = 1 → Ψ k = 1 := by
  intro k hk
  have hΨ' : ∀ u : GroupApproximation.SteinbergGroup (Fin 3) BinL, projection u = 1 →
      QuotientGroup.mk' Ψ.ker (LVCentral.castSuccStab 3 BinL u) = 1 := by
    intro u hu
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', MonoidHom.mem_ker]
    exact hΨ u hu
  have hq : QuotientGroup.mk' Ψ.ker k = 1 :=
    map_ker_eq_one_of_stab_type (QuotientGroup.mk' Ψ.ker) hΨ' k hk
  rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', MonoidHom.mem_ker] at hq
  exact hq

end

end LVRelBrown
end Full
end GroupApproximation
