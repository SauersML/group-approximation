import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CriterionSetup
import GroupApproximation.Meta.AxiomGuard

/-!
# The Steinberg comparison criterion II: the two inputs (lane sk-leavitt-14)

Khanh (arXiv:2609.08428), proof of Theorem 5.1.  Put `J = vertexStab`, `τ = swapLast` and
`h = swapMid`.  Brown's presentation is

  `Π = ⟨J, T | J-multiplication, T k T⁻¹ = τ k τ⁻¹ (k ∈ K = J ∩ Stab(e₂)), T h T = h T h⟩`,

and `p : Π → GL_4(L)`, `j ↦ j`, `T ↦ τ` is an isomorphism, because the frame complex `X_4(L)` is
simply connected.  Its vertices are frame vectors (`FrameFan.FrameVertex`), and simple
connectivity is `FrameFan.binaryLeavitt_frameComplexFour_simplyConnected_of_frameConeFour`.

Neither the isomorphism `p` nor the lift `σ : J → St_4(L)` is on disk in the form that lane 14
consumes (lanes 06–13 run in parallel).  So this file states them.

* `BrownExtensionStatement`: the universal property of `Π ≅ GL_4(L)`, specialized to the target
  group `St_4(L)`.
* `RankFourLiftStatement`: from `stab (K₂(3, L)) = ⊥`, a homomorphism `σ : J → St_4(L)` that
  sends `1 + E_{ij}(a)` (`j ≠ 3`) to `x_{ij}(a)` and satisfies the edge and triangle relations
  with `T = w_{32}`.

The gap is `RankFourCriterionInputsStatement`, their conjunction.

## Why the gap is true

* Brown extension.  If `(f, t)` satisfies the relations of `Π`, then `f` and `t` define
  `Π → St_4(L)`, and composing with `p⁻¹` gives `F`.  Here `p` is an isomorphism by Khanh Theorem
  5.1 (Brown's criterion plus simple connectivity of `X_4(L)`).
* Lift.  `K₂(4, L) = ⊥` (Khanh Theorem 5.4) and `GL_4(L) = E_4(L)`, so `projection` is a
  bijection onto `GL_4(L)`.  Take `σ = projection⁻¹|_J`.  Then `projection x_{ij}(a) = 1 + E_{ij}(a)`,
  and the edge and triangle relations hold after projection.  The edge relation is conjugation by
  `τ`.  The triangle relation `τhτ = hτh` is the braid relation of the transpositions `(32)` and
  `(21)`, which are the images of `w_{32}` and `w_{21}` in characteristic two.

## Why the gap is strictly smaller than the target

The target `stab K₂(3) = ⊥ → K₂(4) = ⊥` is Khanh's whole criterion.  The inputs split off its two
independent halves: the combinatorial Brown presentation (lanes 06–12), and the vertex lift
`σ = ℓ ⋉ x_last` built from `VertexLift.liftGL` and `rowVec` (lanes 05, 13).  Neither input
mentions `K₂(4)`.  The step that combines them is proved in `Criterion`: generation of `St_4(L)`
by the lifted roots and `w_{32}`, the retraction `F ∘ projection = id`, and `K2_eq_bot_iff`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Criterion

open GroupApproximation.BooneHigman.SteinbergBasic
open scoped Matrix

noncomputable section

/-- **Brown's edge relation** `T k T⁻¹ = τ k τ⁻¹` for `k ∈ K = J ∩ Stab(e₂)`, for a candidate
`f : J → H` and `T ↦ t`.  The conjugate `τ k τ⁻¹` lies in `J` and is quantified as `k'`. -/
def EdgeRelation (f : vertexStab →* St 4 BinL) (t : St 4 BinL) : Prop :=
  ∀ k k' : vertexStab, ((k : GLFour) : Matrix (Fin 4) (Fin 4) BinL) *ᵥ prevCol = prevCol →
    (k' : GLFour) = swapLast * (k : GLFour) * swapLast⁻¹ → t * f k * t⁻¹ = f k'

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Criterion.EdgeRelation

/-- **Brown's triangle relation** `T h T = h T h`, with `h = swapMid ∈ J`. -/
def TriangleRelation (f : vertexStab →* St 4 BinL) (t : St 4 BinL) : Prop :=
  ∀ j : vertexStab, (j : GLFour) = swapMid → t * f j * t = f j * t * f j

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Criterion.TriangleRelation

/-- **Interface of lanes sk-leavitt-06…12** (Khanh Theorem 5.1, Brown's presentation): the
universal property of `GL_4(L) ≅ Π`, specialized to the target group `St_4(L)`.  Every pair
`(f, t)` satisfying Brown's relations extends to `F : GL_4(L) → St_4(L)`, with `F|_J = f` and
`F τ = t`.

*Why it is true.*  See the module docstring: `p : Π → GL_4(L)` is an isomorphism, and
`(f, t)` defines `Π → St_4(L)`.  Not proved in this lane. -/
def BrownExtensionStatement : Prop :=
  ∀ (f : vertexStab →* St 4 BinL) (t : St 4 BinL), EdgeRelation f t → TriangleRelation f t →
    ∃ F : GLFour →* St 4 BinL, (∀ j : vertexStab, F (j : GLFour) = f j) ∧ F swapLast = t

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Criterion.BrownExtensionStatement

/-- `σ` sends the elementary matrices of `J` to the Steinberg generators. -/
def LiftsRoots (σ : vertexStab →* St 4 BinL) : Prop :=
  ∀ (i j : Fin 4) (hij : i ≠ j) (hj : j ≠ 3) (a : BinL),
    σ ⟨GroupApproximation.elementaryUnit i j hij a, elementaryUnit_mem_vertexStab i j hij hj a⟩ =
      GroupApproximation.SteinbergGroup.x i j hij a

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Criterion.LiftsRoots

/-- **Interface of lanes sk-leavitt-05 and 13** (Khanh, proof of Theorem 5.1): from
`stab (K₂(3, L)) = ⊥`, a section `σ : J → St_4(L)` over the elementary roots.  It satisfies
Brown's relations with `T = w_{32}`.

*Why it is true.*  Its conclusion holds outright, with `σ = projection⁻¹|_J`, because
`K₂(4, L) = ⊥` and `GL_4(L) = E_4(L)` (Khanh Theorems 5.1 and 5.4).  The intended proof is Khanh's
`σ(M, b) = ℓ(M) · x_last(b)`, built from `VertexLift.liftGL` and `rowVec`.  Not proved in this
lane. -/
def RankFourLiftStatement : Prop :=
  EndpointInterfaces.BinaryLeavittStabKernelThreeTrivialStatement →
    ∃ σ : vertexStab →* St 4 BinL,
      LiftsRoots σ ∧ EdgeRelation σ weylLast ∧ TriangleRelation σ weylLast

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Criterion.RankFourLiftStatement

/-- **The remaining gap of lane sk-leavitt-14**: Brown's extension property and the vertex
lift.  It is true and strictly smaller than the target; see the module docstring. -/
def RankFourCriterionInputsStatement : Prop :=
  BrownExtensionStatement ∧ RankFourLiftStatement

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Criterion.RankFourCriterionInputsStatement

end

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Criterion
