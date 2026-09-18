import GroupApproximation.BooneHigman.Metabelian.ElemFPK2VdKParabolic
import GroupApproximation.BooneHigman.Metabelian.VdKStabRows
import GroupApproximation.Meta.AxiomGuard

/-!
# The row action of `St_m(R)` on `R^m`

Lane `bh-met-91e`, first step of van der Kallen's elementary route to injective stability.
For a commutative ring `R`, `St_m(R)` acts on the right on rows `u : Fin m → R` through its
elementary matrices, `u ↦ u ᵥ* M_g` with `M_g = projectionMatrix g`.

* `vdkInjDirect_Reach u w`: some `g : St_m(R)` sends `u` to `w`.  It is an equivalence relation
  (`vdkInjDirect_reach_refl`, `_trans`, `_symm`).
* `vdkInjDirect_vecMul_elementary`: `u ᵥ* (1 + a E_{ij}) = u + (u_i a) e_j`.
* `vdkInjDirect_reach_step`: one root `x_{ij}(a)` adds `u_i a` to coordinate `j`.
* `vdkInjDirect_reach_add_sum`: a finite batch of such moves, as long as no target coordinate
  is a source coordinate.  The source coordinates then never change along the way.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
  (projectionMatrix projectionMatrix_mul projectionMatrix_one projectionMatrix_x)
open scoped Matrix

variable {R : Type*} [CommRing R] {m : ℕ}

/-- The row `u` is carried to `w` by some element of `St_m(R)`, acting on the right through its
elementary matrix. -/
def vdkInjDirect_Reach (u w : Fin m → R) : Prop :=
  ∃ g : St m R, u ᵥ* projectionMatrix g = w

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjDirect_Reach

theorem vdkInjDirect_reach_refl (u : Fin m → R) : vdkInjDirect_Reach u u := by
  refine ⟨1, ?_⟩
  show u ᵥ* projectionMatrix (1 : St m R) = u
  rw [projectionMatrix_one, Matrix.vecMul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjDirect_reach_refl

theorem vdkInjDirect_reach_trans {u v w : Fin m → R} (h₁ : vdkInjDirect_Reach u v)
    (h₂ : vdkInjDirect_Reach v w) : vdkInjDirect_Reach u w := by
  obtain ⟨g, rfl⟩ := h₁
  obtain ⟨g', rfl⟩ := h₂
  refine ⟨g * g', ?_⟩
  show u ᵥ* projectionMatrix (g * g') = u ᵥ* projectionMatrix g ᵥ* projectionMatrix g'
  rw [projectionMatrix_mul, Matrix.vecMul_vecMul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjDirect_reach_trans

theorem vdkInjDirect_reach_symm {u w : Fin m → R} (h : vdkInjDirect_Reach u w) :
    vdkInjDirect_Reach w u := by
  obtain ⟨g, rfl⟩ := h
  refine ⟨g⁻¹, ?_⟩
  show u ᵥ* projectionMatrix g ᵥ* projectionMatrix g⁻¹ = u
  rw [Matrix.vecMul_vecMul, ← projectionMatrix_mul, mul_inv_cancel, projectionMatrix_one,
    Matrix.vecMul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjDirect_reach_symm

/-- An elementary matrix acting on a row: `u ᵥ* (1 + a E_{ij}) = u + (u_i a) e_j`. -/
theorem vdkInjDirect_vecMul_elementary (i j : Fin m) (a : R) (u : Fin m → R) :
    u ᵥ* (1 + Matrix.single i j a) = u + Pi.single j (u i * a) := by
  rw [← Matrix.mulVec_transpose, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_single, vdkMulVec_elementary, mul_comm a (u i)]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjDirect_vecMul_elementary

/-- The root `x_{ij}(a)` adds `u_i a` to the coordinate `j` of a row. -/
theorem vdkInjDirect_reach_step (u : Fin m → R) (i j : Fin m) (hij : i ≠ j) (a : R) :
    vdkInjDirect_Reach u (u + Pi.single j (u i * a)) := by
  refine ⟨x i j hij a, ?_⟩
  show u ᵥ* projectionMatrix (x i j hij a) = u + Pi.single j (u i * a)
  rw [projectionMatrix_x, vdkInjDirect_vecMul_elementary]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjDirect_reach_step

/-- A batch of root moves: add `u_{src k} c_k` to the coordinate `tgt k` for every `k ∈ s`.
No target coordinate may be a source coordinate, so the sources never change. -/
theorem vdkInjDirect_reach_add_sum {ι : Type*} (s : Finset ι) (u : Fin m → R)
    (src tgt : ι → Fin m) (h : ∀ k l, tgt l ≠ src k) (c : ι → R) :
    vdkInjDirect_Reach u
      (u + ∑ k ∈ s, (Pi.single (tgt k) (u (src k) * c k) : Fin m → R)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, add_zero]
    exact vdkInjDirect_reach_refl u
  | insert k s hk ih =>
    refine vdkInjDirect_reach_trans ih ?_
    have hfix : (u + ∑ l ∈ s, (Pi.single (tgt l) (u (src l) * c l) : Fin m → R)) (src k) =
        u (src k) := by
      rw [Pi.add_apply, Finset.sum_apply, Finset.sum_eq_zero, add_zero]
      intro l _
      exact Pi.single_eq_of_ne (h k l).symm _
    have hstep := vdkInjDirect_reach_step
      (u + ∑ l ∈ s, (Pi.single (tgt l) (u (src l) * c l) : Fin m → R)) (src k) (tgt k)
      (h k k).symm (c k)
    rw [hfix] at hstep
    rw [Finset.sum_insert hk]
    convert hstep using 1
    abel

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjDirect_reach_add_sum

end GroupApproximation.BooneHigman.Metabelian.ElemFP
