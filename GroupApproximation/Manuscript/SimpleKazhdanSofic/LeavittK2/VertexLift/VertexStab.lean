import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.LiftGL
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CriterionSetup
import GroupApproximation.Meta.AxiomGuard

/-!
# Block coordinates on the vertex stabilizer `J ≤ GL_4(L)` (lane sk-leavitt-05)

Khanh (arXiv:2609.08428), proof of Theorem 5.1: `J` is the stabilizer of the last basis vector.
The subgroup is already on disk as `Criterion.vertexStab = {g | g e₃ = e₃}` (lane 14), and this
lane uses it.  In block form (index `last` is mirrored from Khanh's `1`) its elements are
`j(b, H) = [[H, 0], [b, 1]]` with `H ∈ GL_3(L)` and `b ∈ L^3`.

This file proves:

* `mat_col`: the last column of `g ∈ J` is `e_last`;
* `upperBlock : J →* M_3(L)` and `blockUnits : J →* GL_3(L)`, which read off `H`;
* `bottomRow g = b`, with `bottomRow_mul`: `b(gk) = b(g) · H(k) + b(k)`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift

open scoped Matrix

local notation "𝓛" => GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)

/-- The underlying `4 × 4` matrix of an element of `J`. -/
def mat (g : Criterion.vertexStab) : Matrix (Fin 4) (Fin 4) 𝓛 :=
  ((g : (Matrix (Fin 4) (Fin 4) 𝓛)ˣ) : Matrix (Fin 4) (Fin 4) 𝓛)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.mat

theorem mat_mul (g k : Criterion.vertexStab) : mat (g * k) = mat g * mat k :=
  rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.mat_mul

theorem mat_one : mat (1 : Criterion.vertexStab) = 1 :=
  rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.mat_one

/-- The last column of `g ∈ J` is `e_last`. -/
theorem mat_col (g : Criterion.vertexStab) (i : Fin 4) :
    mat g i (Fin.last 3) = (1 : Matrix (Fin 4) (Fin 4) 𝓛) i (Fin.last 3) := by
  have hg : ((g : (Matrix (Fin 4) (Fin 4) 𝓛)ˣ) : Matrix (Fin 4) (Fin 4) 𝓛) *ᵥ
      Pi.single (Fin.last 3) (1 : 𝓛) = Pi.single (Fin.last 3) (1 : 𝓛) := g.2
  have h1 := congrFun hg i
  rw [Matrix.mulVec_single_one, Pi.single_apply] at h1
  rw [Matrix.one_apply]
  exact h1

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.mat_col

theorem mat_castSucc_last (g : Criterion.vertexStab) (i : Fin 3) :
    mat g i.castSucc (Fin.last 3) = 0 := by
  rw [mat_col, Matrix.one_apply_ne (Fin.castSucc_ne_last i)]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.mat_castSucc_last

theorem mat_last_last (g : Criterion.vertexStab) : mat g (Fin.last 3) (Fin.last 3) = 1 := by
  rw [mat_col, Matrix.one_apply_eq]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.mat_last_last

theorem one_castSucc_castSucc (i j : Fin 3) :
    (1 : Matrix (Fin 4) (Fin 4) 𝓛) i.castSucc j.castSucc = (1 : Matrix (Fin 3) (Fin 3) 𝓛) i j := by
  by_cases hij : i = j
  · rw [hij, Matrix.one_apply_eq, Matrix.one_apply_eq]
  · have hne : i.castSucc ≠ j.castSucc := fun h => hij (Fin.castSucc_inj.mp h)
    rw [Matrix.one_apply_ne hne, Matrix.one_apply_ne hij]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.one_castSucc_castSucc

theorem one_castSucc_last (i : Fin 3) :
    (1 : Matrix (Fin 4) (Fin 4) 𝓛) i.castSucc (Fin.last 3) = 0 :=
  Matrix.one_apply_ne (Fin.castSucc_ne_last i)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.one_castSucc_last

theorem mat_mul_castSucc_castSucc (g k : Criterion.vertexStab) (i j : Fin 3) :
    mat (g * k) i.castSucc j.castSucc =
      ∑ l : Fin 3, mat g i.castSucc l.castSucc * mat k l.castSucc j.castSucc := by
  rw [mat_mul, Matrix.mul_apply, Fin.sum_univ_castSucc, mat_castSucc_last, zero_mul, add_zero]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.mat_mul_castSucc_castSucc

/-- The block `H` of `j(b, H) = [[H, 0], [b, 1]]`, as a monoid homomorphism. -/
def upperBlock : Criterion.vertexStab →* Matrix (Fin 3) (Fin 3) 𝓛 where
  toFun g := Matrix.of fun i j => mat g i.castSucc j.castSucc
  map_one' := by
    ext i j
    show mat 1 i.castSucc j.castSucc = (1 : Matrix (Fin 3) (Fin 3) 𝓛) i j
    rw [mat_one, one_castSucc_castSucc]
  map_mul' g k := by
    ext i j
    show mat (g * k) i.castSucc j.castSucc =
      ∑ l : Fin 3, mat g i.castSucc l.castSucc * mat k l.castSucc j.castSucc
    exact mat_mul_castSucc_castSucc g k i j

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.upperBlock

theorem upperBlock_apply (g : Criterion.vertexStab) (i j : Fin 3) :
    upperBlock g i j = mat g i.castSucc j.castSucc :=
  rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.upperBlock_apply

/-- The block `H ∈ GL_3(L)` of an element of `J`. -/
def blockUnits : Criterion.vertexStab →* (Matrix (Fin 3) (Fin 3) 𝓛)ˣ :=
  upperBlock.toHomUnits

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.blockUnits

theorem blockUnits_val (g : Criterion.vertexStab) :
    ((blockUnits g : (Matrix (Fin 3) (Fin 3) 𝓛)ˣ) : Matrix (Fin 3) (Fin 3) 𝓛) = upperBlock g :=
  rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.blockUnits_val

/-- The row `b` of `j(b, H) = [[H, 0], [b, 1]]`. -/
def bottomRow (g : Criterion.vertexStab) : Fin 3 → 𝓛 :=
  fun j => mat g (Fin.last 3) j.castSucc

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.bottomRow

theorem bottomRow_apply (g : Criterion.vertexStab) (j : Fin 3) :
    bottomRow g j = mat g (Fin.last 3) j.castSucc :=
  rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.bottomRow_apply

/-- `[[H, 0], [b, 1]] · [[K, 0], [c, 1]] = [[HK, 0], [bK + c, 1]]`. -/
theorem bottomRow_mul (g k : Criterion.vertexStab) :
    bottomRow (g * k) = bottomRow g ᵥ* upperBlock k + bottomRow k := by
  funext j
  rw [Pi.add_apply, Matrix.vecMul_apply_eq_sum]
  simp only [bottomRow_apply, upperBlock_apply]
  rw [mat_mul, Matrix.mul_apply, Fin.sum_univ_castSucc, mat_last_last, one_mul]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.bottomRow_mul

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift
