import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVAssembly.Setup

/-!
# Brown's relations and the retraction `F ∘ projection = id` (glue for `K₂(4, L) = ⊥`)

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-735.  This is the final step of the proof
of Khanh (arXiv:2609.08428), Thm 5.1.  Let `σ : J → St_4(L)` send `1 + E_{ij}(a)` (`j ≠ 3`) to
`x_{ij}(a)`, and let `F : GL_4(L) → St_4(L)` extend `σ` with `F τ = w₃₂`.  Then `F ∘ projection`
fixes a generating set of `St_4(L)`, so it is the identity and `projection` is injective.

* `EdgeRelation`, `TriangleRelation`, `LiftsRoots`: the properties of a candidate `(σ, t)`.
* `lift_projection_eq`: the retraction.
* `projection_injective_of_extension`: `St_4(L) → E_4(L)` is injective.

This ports the unwired foreign drafts `LeavittK2/{CriterionInterfaces,Criterion}.lean`.  Brown's
extension property is not a hypothesis here: `F` is an explicit argument.
-/

namespace GroupApproximation.Full.LVAssembly

open scoped Matrix

noncomputable section

/-- **Brown's edge relation** `T k T⁻¹ = f(τ k τ⁻¹)` for `k ∈ J ∩ Stab(e₂)` (Khanh, Thm 5.1). -/
def EdgeRelation (f : vertexStab →* GroupApproximation.SteinbergGroup (Fin 4) BinL)
    (t : GroupApproximation.SteinbergGroup (Fin 4) BinL) : Prop :=
  ∀ k k' : vertexStab, ((k : GLFour) : Matrix (Fin 4) (Fin 4) BinL) *ᵥ prevCol = prevCol →
    (k' : GLFour) = swapLast * (k : GLFour) * swapLast⁻¹ → t * f k * t⁻¹ = f k'

/-- **Brown's triangle relation** `T h T = h T h`, `h = swapMid ∈ J` (Khanh, Thm 5.1). -/
def TriangleRelation (f : vertexStab →* GroupApproximation.SteinbergGroup (Fin 4) BinL)
    (t : GroupApproximation.SteinbergGroup (Fin 4) BinL) : Prop :=
  ∀ j : vertexStab, (j : GLFour) = swapMid → t * f j * t = f j * t * f j

/-- `σ` sends the elementary matrices of `J` to the Steinberg generators. -/
def LiftsRoots (σ : vertexStab →* GroupApproximation.SteinbergGroup (Fin 4) BinL) : Prop :=
  ∀ (i j : Fin 4) (hij : i ≠ j) (hj : j ≠ 3) (a : BinL),
    σ ⟨GroupApproximation.elementaryUnit i j hij a, elementaryUnit_mem_vertexStab i j hij hj a⟩ =
      GroupApproximation.SteinbergGroup.x i j hij a

/-- The loop `St_4(L) → E_4(L) ⊆ GL_4(L) → St_4(L)` through a candidate extension `F`. -/
def projectionLoop (F : GLFour →* GroupApproximation.SteinbergGroup (Fin 4) BinL) :
    GroupApproximation.SteinbergGroup (Fin 4) BinL →*
      GroupApproximation.SteinbergGroup (Fin 4) BinL :=
  F.comp ((GroupApproximation.elementaryGroup (Fin 4) BinL).subtype.comp
    GroupApproximation.SteinbergGroup.projection)

/-- **The retraction** (Khanh, Thm 5.1).  An extension `F` of a root-lifting `σ` with
`F τ = w₃₂` is a left inverse of `projection`. -/
theorem lift_projection_eq (σ : vertexStab →* GroupApproximation.SteinbergGroup (Fin 4) BinL)
    (F : GLFour →* GroupApproximation.SteinbergGroup (Fin 4) BinL)
    (hroot : LiftsRoots σ) (hFJ : ∀ j : vertexStab, F (j : GLFour) = σ j)
    (hFτ : F swapLast = weylLast) (g : GroupApproximation.SteinbergGroup (Fin 4) BinL) :
    F ((GroupApproximation.SteinbergGroup.projection g :
      GroupApproximation.elementaryGroup (Fin 4) BinL) : GLFour) = g := by
  have hS : (projectionLoop F).eqLocus
      (MonoidHom.id (GroupApproximation.SteinbergGroup (Fin 4) BinL)) = ⊤ := by
    refine steinberg_eq_top_of_mem _ ?_ ?_
    · intro i j hij hj a
      show F ((GroupApproximation.SteinbergGroup.projection
          (GroupApproximation.SteinbergGroup.x i j hij a) :
            GroupApproximation.elementaryGroup (Fin 4) BinL) : GLFour) =
        GroupApproximation.SteinbergGroup.x i j hij a
      rw [GroupApproximation.SteinbergGroup.projection_x]
      exact (hFJ ⟨GroupApproximation.elementaryUnit i j hij a,
        elementaryUnit_mem_vertexStab i j hij hj a⟩).trans (hroot i j hij hj a)
    · show F swapLast = weylLast
      exact hFτ
  have hg : g ∈ (projectionLoop F).eqLocus
      (MonoidHom.id (GroupApproximation.SteinbergGroup (Fin 4) BinL)) := by
    rw [hS]
    exact Subgroup.mem_top g
  exact hg

/-- **`St_4(L) → E_4(L)` is injective**, given a root-lifting `σ : J → St_4(L)` and an extension
`F : GL_4(L) → St_4(L)` of `σ` with `F τ = w₃₂` (Khanh, Thm 5.1; tex l.733-735). -/
theorem projection_injective_of_extension
    (σ : vertexStab →* GroupApproximation.SteinbergGroup (Fin 4) BinL)
    (F : GLFour →* GroupApproximation.SteinbergGroup (Fin 4) BinL)
    (hroot : LiftsRoots σ) (hFJ : ∀ j : vertexStab, F (j : GLFour) = σ j)
    (hFτ : F swapLast = weylLast) :
    Function.Injective
      (GroupApproximation.SteinbergGroup.projection (I := Fin 4) (R := BinL)) := by
  intro g g' hgg'
  calc g = F ((GroupApproximation.SteinbergGroup.projection g :
          GroupApproximation.elementaryGroup (Fin 4) BinL) : GLFour) :=
        (lift_projection_eq σ F hroot hFJ hFτ g).symm
    _ = F ((GroupApproximation.SteinbergGroup.projection g' :
          GroupApproximation.elementaryGroup (Fin 4) BinL) : GLFour) := by
        rw [hgg']
    _ = g' := lift_projection_eq σ F hroot hFJ hFτ g'

end

end GroupApproximation.Full.LVAssembly
