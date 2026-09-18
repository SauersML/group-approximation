import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVAssembly.FrameSwaps
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVAssembly.EdgeRelation
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVBrown.BrownLift
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFrame.Main

/-!
# Brown's criterion for `GL_4(L)` on the frame complex (glue for `K₂(4, L) = ⊥`)

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-735.  This is part of the proof of
Khanh (arXiv:2609.08428), Thm 5.1, over `L = L_{𝔽₂}(1,2)`.

`GL_4(L)` acts on the frame complex `X₄(L)`, which is simply connected (leaf T1c,
`frameComplexFour_simplyConnected`).  Brown's criterion (leaf T1d,
`GroupApproximation.Full.LVBrown.brown_lift`) extends a homomorphism on the stabilizer `J` of `e₃`
to all of `GL_4(L)` once the edge relation, `t² = f(τ²)` and the triangle relation hold.

* `stabSection σ`: a homomorphism `σ : J → St_4(L)`, on the stabilizer of the base vertex.
* `projection_injective_of_liftsRoots`: if `σ` sends each elementary matrix of `J` to its
  Steinberg generator (`LiftsRoots`), then `St_4(L) → E_4(L)` is injective.  The edge and
  triangle relations are `edgeRelation_of_liftsRoots` and `triangleRelation_of_liftsRoots`, and
  the extension is a retraction of the projection (`projection_injective_of_extension`).
-/

namespace GroupApproximation.Full.LVAssembly

open scoped Matrix
open GroupApproximation.Full.LVFrame

noncomputable section

/-- A homomorphism on `J`, restricted to the stabilizer of the base vertex `e₃`. -/
def stabSection (σ : vertexStab →* GroupApproximation.SteinbergGroup (Fin 4) BinL) :
    MulAction.stabilizer GLFour baseVertex →* GroupApproximation.SteinbergGroup (Fin 4) BinL :=
  σ.comp (Subgroup.inclusion stabilizer_eq_vertexStab.le)

theorem stabSection_apply (σ : vertexStab →* GroupApproximation.SteinbergGroup (Fin 4) BinL)
    (a : MulAction.stabilizer GLFour baseVertex) :
    stabSection σ a = σ (Subgroup.inclusion stabilizer_eq_vertexStab.le a) :=
  rfl

/-- **`St_4(L) → E_4(L)` is injective, given a root lift on `J`** (Khanh, Thm 5.1;
tex l.733-735).  Brown's criterion extends `σ` to `F : GL_4(L) → St_4(L)` with `F τ = w₃₂`, and
such an extension retracts the projection. -/
theorem projection_injective_of_liftsRoots
    (σ : vertexStab →* GroupApproximation.SteinbergGroup (Fin 4) BinL) (hσ : LiftsRoots σ) :
    Function.Injective
      (GroupApproximation.SteinbergGroup.projection (I := Fin 4) (R := BinL)) := by
  have hτ2 : (swapLast * swapLast) • baseVertex = baseVertex := by
    rw [swapLast_mul_self, one_smul]
  have hh0 : swapMid • baseVertex = baseVertex := swapMid_smul_base
  have hedge : ∀ a b : MulAction.stabilizer GLFour baseVertex,
      (a : GLFour) • nextVertex = nextVertex → (b : GLFour) = swapLast * a * swapLast⁻¹ →
        weylLast * stabSection σ a * weylLast⁻¹ = stabSection σ b := by
    intro a b ha hb
    have ha' : (((Subgroup.inclusion stabilizer_eq_vertexStab.le a : vertexStab) : GLFour) :
        Matrix (Fin 4) (Fin 4) BinL) *ᵥ prevCol = prevCol := congrArg Subtype.val ha
    exact edgeRelation_of_liftsRoots σ hσ (Subgroup.inclusion stabilizer_eq_vertexStab.le a)
      (Subgroup.inclusion stabilizer_eq_vertexStab.le b) ha' hb
  have hone : Subgroup.inclusion stabilizer_eq_vertexStab.le
      (⟨swapLast * swapLast, hτ2⟩ : MulAction.stabilizer GLFour baseVertex) = 1 :=
    Subtype.ext swapLast_mul_self
  have ht2 : weylLast * weylLast = stabSection σ ⟨swapLast * swapLast, hτ2⟩ := by
    rw [weylLast_mul_self, stabSection_apply, hone, map_one]
  have hbr : weylLast * stabSection σ ⟨swapMid, hh0⟩ * weylLast =
      stabSection σ ⟨swapMid, hh0⟩ * weylLast * stabSection σ ⟨swapMid, hh0⟩ :=
    triangleRelation_of_liftsRoots σ hσ
      (Subgroup.inclusion stabilizer_eq_vertexStab.le ⟨swapMid, hh0⟩) rfl
  obtain ⟨F, hFf, hFτ⟩ := GroupApproximation.Full.LVBrown.brown_lift (frameComplexFour BinL)
    frameAction frameComplexFour_simplyConnected baseVertex nextVertex baseEdge
    frame_edge_transitive swapLast swapMid swapLast_smul_base swapLast_smul_next hh0
    swapMid_mul_self swap_braid frame_tri_transitive closure_stabilizer_swapLast
    (stabSection σ) weylLast hedge hτ2 ht2 hbr
  exact projection_injective_of_extension σ F hσ
    (fun j => hFf ⟨(j : GLFour), stabilizer_eq_vertexStab.ge j.2⟩) hFτ

end

end GroupApproximation.Full.LVAssembly
