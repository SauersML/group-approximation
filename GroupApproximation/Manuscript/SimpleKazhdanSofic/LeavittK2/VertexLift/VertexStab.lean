import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.LiftGL
import GroupApproximation.Meta.AxiomGuard

/-!
# The vertex stabilizer `J ≤ GL_4(L)` (lane sk-leavitt-05)

Khanh (arXiv:2609.08428), proof of Theorem 5.1: `J` is the stabilizer of the last basis vector,
i.e. the units whose last column is `e_last`.  In block form (index `last` is mirrored from
Khanh's `1`) its elements are `j(b, H) = [[H, 0], [b, 1]]` with `H ∈ GL_3(L)` and `b ∈ L^3`.

This file proves:

* `vertexStab`, the subgroup;
* `upperBlock : J →* M_3(L)` and `blockUnits : J →* GL_3(L)`, which read off `H`;
* `bottomRow g = b`, with `bottomRow_mul`: `b(gk) = b(g) · H(k) + b(k)`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift

open scoped Matrix

local notation "𝓛" => GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)

/-- **The vertex stabilizer** `J ≤ GL_4(L)`: the units whose last column is `e_last`. -/
def vertexStab : Subgroup (Matrix (Fin 4) (Fin 4) 𝓛)ˣ where
  carrier := {g | ∀ i : Fin 4, (g : Matrix (Fin 4) (Fin 4) 𝓛) i (Fin.last 3) =
    (1 : Matrix (Fin 4) (Fin 4) 𝓛) i (Fin.last 3)}
  mul_mem' := by
    intro g k hg hk
    have hg' : ∀ i : Fin 4, (g : Matrix (Fin 4) (Fin 4) 𝓛) i (Fin.last 3) =
        (1 : Matrix (Fin 4) (Fin 4) 𝓛) i (Fin.last 3) := hg
    have hk' : ∀ i : Fin 4, (k : Matrix (Fin 4) (Fin 4) 𝓛) i (Fin.last 3) =
        (1 : Matrix (Fin 4) (Fin 4) 𝓛) i (Fin.last 3) := hk
    show ∀ i : Fin 4, ((g * k : (Matrix (Fin 4) (Fin 4) 𝓛)ˣ) : Matrix (Fin 4) (Fin 4) 𝓛) i
      (Fin.last 3) = (1 : Matrix (Fin 4) (Fin 4) 𝓛) i (Fin.last 3)
    intro i
    have h1 := congrArg (fun M : Matrix (Fin 4) (Fin 4) 𝓛 => M i (Fin.last 3))
      (Matrix.mul_one (g : Matrix (Fin 4) (Fin 4) 𝓛))
    simp only [Matrix.mul_apply] at h1
    rw [Units.val_mul, Matrix.mul_apply]
    simp only [hk']
    rw [h1]
    exact hg' i
  one_mem' := by
    show ∀ i : Fin 4, ((1 : (Matrix (Fin 4) (Fin 4) 𝓛)ˣ) : Matrix (Fin 4) (Fin 4) 𝓛) i
      (Fin.last 3) = (1 : Matrix (Fin 4) (Fin 4) 𝓛) i (Fin.last 3)
    intro i
    rfl
  inv_mem' := by
    intro g hg
    have hg' : ∀ i : Fin 4, (g : Matrix (Fin 4) (Fin 4) 𝓛) i (Fin.last 3) =
        (1 : Matrix (Fin 4) (Fin 4) 𝓛) i (Fin.last 3) := hg
    show ∀ i : Fin 4, ((g⁻¹ : (Matrix (Fin 4) (Fin 4) 𝓛)ˣ) : Matrix (Fin 4) (Fin 4) 𝓛) i
      (Fin.last 3) = (1 : Matrix (Fin 4) (Fin 4) 𝓛) i (Fin.last 3)
    intro i
    have hinv : ((g⁻¹ : (Matrix (Fin 4) (Fin 4) 𝓛)ˣ) : Matrix (Fin 4) (Fin 4) 𝓛) *
        (g : Matrix (Fin 4) (Fin 4) 𝓛) = 1 := by
      rw [Units.inv_mul]
    have h1 := congrArg (fun M : Matrix (Fin 4) (Fin 4) 𝓛 => M i (Fin.last 3)) hinv
    have h2 := congrArg (fun M : Matrix (Fin 4) (Fin 4) 𝓛 => M i (Fin.last 3))
      (Matrix.mul_one ((g⁻¹ : (Matrix (Fin 4) (Fin 4) 𝓛)ˣ) : Matrix (Fin 4) (Fin 4) 𝓛))
    simp only [Matrix.mul_apply, hg'] at h1
    simp only [Matrix.mul_apply] at h2
    rw [← h2]
    exact h1

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.vertexStab

/-- The underlying `4 × 4` matrix of an element of `J`. -/
def mat (g : vertexStab) : Matrix (Fin 4) (Fin 4) 𝓛 :=
  ((g : (Matrix (Fin 4) (Fin 4) 𝓛)ˣ) : Matrix (Fin 4) (Fin 4) 𝓛)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.mat

theorem mat_mul (g k : vertexStab) : mat (g * k) = mat g * mat k :=
  rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.mat_mul

theorem mat_one : mat (1 : vertexStab) = 1 :=
  rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.mat_one

theorem mat_col (g : vertexStab) (i : Fin 4) :
    mat g i (Fin.last 3) = (1 : Matrix (Fin 4) (Fin 4) 𝓛) i (Fin.last 3) := by
  have hg : ∀ i : Fin 4, ((g : (Matrix (Fin 4) (Fin 4) 𝓛)ˣ) : Matrix (Fin 4) (Fin 4) 𝓛) i
      (Fin.last 3) = (1 : Matrix (Fin 4) (Fin 4) 𝓛) i (Fin.last 3) := g.2
  exact hg i

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.mat_col

theorem mat_castSucc_last (g : vertexStab) (i : Fin 3) : mat g i.castSucc (Fin.last 3) = 0 := by
  rw [mat_col, Matrix.one_apply_ne (Fin.castSucc_ne_last i)]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.mat_castSucc_last

theorem mat_last_last (g : vertexStab) : mat g (Fin.last 3) (Fin.last 3) = 1 := by
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

theorem mat_mul_castSucc_castSucc (g k : vertexStab) (i j : Fin 3) :
    mat (g * k) i.castSucc j.castSucc =
      ∑ l : Fin 3, mat g i.castSucc l.castSucc * mat k l.castSucc j.castSucc := by
  rw [mat_mul, Matrix.mul_apply, Fin.sum_univ_castSucc, mat_castSucc_last, zero_mul, add_zero]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.mat_mul_castSucc_castSucc

/-- The block `H` of `j(b, H) = [[H, 0], [b, 1]]`, as a monoid homomorphism. -/
def upperBlock : vertexStab →* Matrix (Fin 3) (Fin 3) 𝓛 where
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

theorem upperBlock_apply (g : vertexStab) (i j : Fin 3) :
    upperBlock g i j = mat g i.castSucc j.castSucc :=
  rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.upperBlock_apply

/-- The block `H ∈ GL_3(L)` of an element of `J`. -/
def blockUnits : vertexStab →* (Matrix (Fin 3) (Fin 3) 𝓛)ˣ :=
  upperBlock.toHomUnits

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.blockUnits

theorem blockUnits_val (g : vertexStab) :
    ((blockUnits g : (Matrix (Fin 3) (Fin 3) 𝓛)ˣ) : Matrix (Fin 3) (Fin 3) 𝓛) = upperBlock g :=
  rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.blockUnits_val

/-- The row `b` of `j(b, H) = [[H, 0], [b, 1]]`. -/
def bottomRow (g : vertexStab) : Fin 3 → 𝓛 :=
  fun j => mat g (Fin.last 3) j.castSucc

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.bottomRow

theorem bottomRow_apply (g : vertexStab) (j : Fin 3) :
    bottomRow g j = mat g (Fin.last 3) j.castSucc :=
  rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.bottomRow_apply

/-- `[[H, 0], [b, 1]] · [[K, 0], [c, 1]] = [[HK, 0], [bK + c, 1]]`. -/
theorem bottomRow_mul (g k : vertexStab) :
    bottomRow (g * k) = bottomRow g ᵥ* upperBlock k + bottomRow k := by
  funext j
  rw [Pi.add_apply, Matrix.vecMul_apply_eq_sum]
  simp only [bottomRow_apply, upperBlock_apply]
  rw [mat_mul, Matrix.mul_apply, Fin.sum_univ_castSucc, mat_last_last, one_mul]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.bottomRow_mul

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift
