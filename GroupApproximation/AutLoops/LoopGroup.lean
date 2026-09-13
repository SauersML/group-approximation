import GroupApproximation.AutLoops.PointNorm
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Homotopy.Product
import Mathlib.GroupTheory.EckmannHilton

/-!
# The loop group `π_1(Aut A, id)`

For a topological group `G`, the pointwise product of loops at `1` descends to `π_1(G, 1)`, is
unital, and satisfies the interchange law with concatenation. By Eckmann–Hilton it is the group
law of `π_1(G, 1)`, which is therefore commutative. `AutLoopGroup A` is `π_1(Aut A, id)` for the
point-norm topology.

## Main declarations

* `loopMul`, `loopMulQ`: the pointwise product of loops and of their homotopy classes.
* `loopMul_trans`: the interchange law `(p₁ ⬝ p₂)(q₁ ⬝ q₂) = p₁q₁ ⬝ p₂q₂`.
* `pointwiseMul_eq_mul`: the pointwise product of classes is the product in `π_1(G, 1)`.
* `instCommGroupFundamentalGroup`: `π_1(G, 1)` is commutative.
* `AutLoopGroup A`: `π_1(PointNormAut A, 1)`.
-/

namespace GroupApproximation
namespace AutLoops

attribute [local instance] Path.Homotopic.setoid

section TopologicalGroup

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

/-- The pointwise product `t ↦ p t * q t` of two loops at `1`. -/
def loopMul (p q : Path (1 : G) 1) : Path (1 : G) 1 where
  toFun t := p t * q t
  continuous_toFun := p.continuous.mul q.continuous
  source' := by simp
  target' := by simp

@[simp] theorem loopMul_apply (p q : Path (1 : G) 1) (t : unitInterval) :
    loopMul p q t = p t * q t := rfl

theorem loopMul_eq_cast (p q : Path (1 : G) 1) :
    loopMul p q = ((p.prod q).map continuous_mul).cast (mul_one (1 : G)).symm
      (mul_one (1 : G)).symm :=
  DFunLike.ext _ _ fun _ => rfl

theorem loopMul_homotopic {p p' q q' : Path (1 : G) 1} (hp : p.Homotopic p')
    (hq : q.Homotopic q') : (loopMul p q).Homotopic (loopMul p' q') := by
  rw [loopMul_eq_cast p q, loopMul_eq_cast p' q']
  exact Path.Homotopic.pathCast
    (Path.Homotopic.map (Nonempty.map2 Path.Homotopic.prodHomotopy hp hq)
      ⟨fun x : G × G => x.1 * x.2, continuous_mul⟩) _ _

/-- The interchange law between the pointwise product and concatenation of loops. -/
theorem loopMul_trans (p₁ p₂ q₁ q₂ : Path (1 : G) 1) :
    loopMul (p₁.trans p₂) (q₁.trans q₂) = (loopMul p₁ q₁).trans (loopMul p₂ q₂) := by
  refine DFunLike.ext _ _ fun t => ?_
  simp only [loopMul_apply, Path.trans_apply]
  split_ifs <;> rfl

theorem loopMul_refl_left (q : Path (1 : G) 1) : loopMul (Path.refl 1) q = q :=
  DFunLike.ext _ _ fun t => one_mul (q t)

theorem loopMul_refl_right (p : Path (1 : G) 1) : loopMul p (Path.refl 1) = p :=
  DFunLike.ext _ _ fun t => mul_one (p t)

/-- The pointwise product of homotopy classes of loops at `1`. -/
def loopMulQ (P Q : Path.Homotopic.Quotient (1 : G) 1) : Path.Homotopic.Quotient (1 : G) 1 :=
  Quotient.map₂ loopMul (fun _ _ hp _ _ hq => loopMul_homotopic hp hq) P Q

@[simp] theorem loopMulQ_mk (p q : Path (1 : G) 1) :
    loopMulQ (.mk p) (.mk q) = Path.Homotopic.Quotient.mk (loopMul p q) := rfl

theorem loopMulQ_trans (P₁ P₂ Q₁ Q₂ : Path.Homotopic.Quotient (1 : G) 1) :
    loopMulQ (P₁.trans P₂) (Q₁.trans Q₂) = (loopMulQ P₁ Q₁).trans (loopMulQ P₂ Q₂) :=
  Path.Homotopic.Quotient.ind₂ (fun p₁ q₁ => Path.Homotopic.Quotient.ind₂ (fun p₂ q₂ =>
    congrArg Path.Homotopic.Quotient.mk (loopMul_trans p₁ p₂ q₁ q₂)) P₂ Q₂) P₁ Q₁

theorem loopMulQ_refl_left (Q : Path.Homotopic.Quotient (1 : G) 1) :
    loopMulQ (.refl 1) Q = Q := by
  induction Q using Path.Homotopic.Quotient.ind with
  | mk q => exact congrArg Path.Homotopic.Quotient.mk (loopMul_refl_left q)

theorem loopMulQ_refl_right (P : Path.Homotopic.Quotient (1 : G) 1) :
    loopMulQ P (.refl 1) = P := by
  induction P using Path.Homotopic.Quotient.ind with
  | mk p => exact congrArg Path.Homotopic.Quotient.mk (loopMul_refl_right p)

/-- The pointwise product on `π_1(G, 1)`. -/
def pointwiseMul (P Q : FundamentalGroup G 1) : FundamentalGroup G 1 :=
  FundamentalGroup.fromPath (loopMulQ P.toPath Q.toPath)

theorem pointwiseMul_isUnital : EckmannHilton.IsUnital (pointwiseMul (G := G)) 1 :=
  EckmannHilton.IsUnital.mk
    { left_id := fun Q => loopMulQ_refl_left Q, right_id := fun P => loopMulQ_refl_right P }

theorem pointwiseMul_distrib (a b c d : FundamentalGroup G 1) :
    pointwiseMul (a * b) (c * d) = pointwiseMul a c * pointwiseMul b d :=
  loopMulQ_trans b a d c

/-- Eckmann–Hilton: the pointwise product of loop classes is the product in `π_1(G, 1)`. -/
theorem pointwiseMul_eq_mul (a b : FundamentalGroup G 1) : pointwiseMul a b = a * b :=
  congrFun (congrFun (EckmannHilton.mul pointwiseMul_isUnital EckmannHilton.MulOneClass.isUnital
    pointwiseMul_distrib) a) b

theorem fromPath_mk_loopMul (p q : Path (1 : G) 1) :
    FundamentalGroup.fromPath (.mk (loopMul p q)) =
      FundamentalGroup.fromPath (.mk p) * FundamentalGroup.fromPath (.mk q) :=
  pointwiseMul_eq_mul (FundamentalGroup.fromPath (.mk p)) (FundamentalGroup.fromPath (.mk q))

/-- `π_1(G, 1)` of a topological group is commutative (Eckmann–Hilton). -/
noncomputable instance instCommGroupFundamentalGroup : CommGroup (FundamentalGroup G 1) :=
  EckmannHilton.commGroup pointwiseMul_isUnital pointwiseMul_distrib

end TopologicalGroup

/-- `π_1(Aut A, id)` for the point-norm topology on `Aut A`. -/
abbrev AutLoopGroup (A : Type*) [CStarAlgebra A] : Type _ := FundamentalGroup (PointNormAut A) 1

end AutLoops
end GroupApproximation
