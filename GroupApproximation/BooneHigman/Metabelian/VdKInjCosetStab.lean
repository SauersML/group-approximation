import GroupApproximation.BooneHigman.Metabelian.VdKInjDirectRow
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2VdKRowCanonical
import GroupApproximation.Meta.AxiomGuard

/-!
# The stabiliser of the last basis row in `St_{n+1}(R)`

Lane `bh-met-91j`, first file.  For a commutative ring `R`, `St_{n+1}(R)` acts on rows
`u : Fin (n+1) → R` on the right, `u ↦ u ᵥ* M_g` with `M_g = projectionMatrix g`.

* `vdkInjCoset_rowStab n R`: the subgroup of `g` with `e_last ᵥ* M_g = e_last`.
* `vdkInjCoset_x_mem`: a root `x_{ij}(a)` with `i ≠ last` fixes `e_last`.  In particular the
  column roots `x_{i,last}(a)` (`vdkInjCoset_colRoot_mem`) and the stabilized roots do.
* `vdkInjCoset_stab_mem`: `stab g` fixes `e_last`, by induction over the generators.
* `vdkInjCoset_colVec_mem`: the column products `colVec v` fix `e_last`.
* `vdkInjCoset_rowPar_le`: the parabolic image `P = vdkRowParSubgroup n R` lies in the stabiliser.
* `vdkInjCoset_K2_le_rowStab`: so does `K₂(n+1, R)`, since its matrices are `1`.

The reverse inclusion `rowStab ≤ P` is Step A of the lane.  It is the named `Prop`
`vdkInjCoset_RowStabAt` of `VdKInjCosetSurj`, and it is not proved here.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
  (colRoot colVec colVec_add colVec_zero projectionMatrix projectionMatrix_mul
    projectionMatrix_one projectionMatrix_x)
open scoped Matrix

variable {n : ℕ} {R : Type*} [CommRing R]

variable (n R) in
/-- The stabiliser of the last basis row `e_last` under the right row action `u ↦ u ᵥ* M_g`. -/
def vdkInjCoset_rowStab : Subgroup (St (n + 1) R) where
  carrier := {g | (Pi.single (Fin.last n) 1 : Fin (n + 1) → R) ᵥ* projectionMatrix g =
    Pi.single (Fin.last n) 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [projectionMatrix_mul, ← Matrix.vecMul_vecMul, ha, hb]
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    rw [projectionMatrix_one, Matrix.vecMul_one]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    calc (Pi.single (Fin.last n) 1 : Fin (n + 1) → R) ᵥ* projectionMatrix a⁻¹
        = ((Pi.single (Fin.last n) 1 : Fin (n + 1) → R) ᵥ* projectionMatrix a) ᵥ*
            projectionMatrix a⁻¹ := by rw [ha]
      _ = Pi.single (Fin.last n) 1 := by
          rw [Matrix.vecMul_vecMul, ← projectionMatrix_mul, mul_inv_cancel, projectionMatrix_one,
            Matrix.vecMul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCoset_rowStab

theorem vdkInjCoset_mem_rowStab (g : St (n + 1) R) :
    g ∈ vdkInjCoset_rowStab n R ↔
      (Pi.single (Fin.last n) 1 : Fin (n + 1) → R) ᵥ* projectionMatrix g =
        Pi.single (Fin.last n) 1 :=
  Iff.rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCoset_mem_rowStab

/-- A root `x_{ij}(a)` whose source index `i` is not `last` fixes `e_last`. -/
theorem vdkInjCoset_x_mem (i j : Fin (n + 1)) (hij : i ≠ j) (a : R) (hi : i ≠ Fin.last n) :
    x i j hij a ∈ vdkInjCoset_rowStab n R := by
  rw [vdkInjCoset_mem_rowStab, projectionMatrix_x, vdkInjDirect_vecMul_elementary,
    Pi.single_apply, if_neg hi, zero_mul, Pi.single_zero, add_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCoset_x_mem

/-- The column root `x_{i,last}(a)` fixes `e_last`. -/
theorem vdkInjCoset_colRoot_mem (i : Fin n) (a : R) :
    colRoot i a ∈ vdkInjCoset_rowStab n R :=
  vdkInjCoset_x_mem i.castSucc (Fin.last n) (Fin.castSucc_ne_last i) a (Fin.castSucc_ne_last i)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCoset_colRoot_mem

/-- A stabilized root `stab x_{ij}(a) = x_{castSucc i, castSucc j}(a)` fixes `e_last`. -/
theorem vdkInjCoset_stab_x_mem (i j : Fin n) (hij : i ≠ j) (a : R) :
    stab n R (x i j hij a) ∈ vdkInjCoset_rowStab n R := by
  rw [stab_x]
  exact vdkInjCoset_x_mem _ _ _ a (Fin.castSucc_ne_last i)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCoset_stab_x_mem

/-- `stab g` fixes `e_last`, by induction over the Steinberg generators. -/
theorem vdkInjCoset_stab_mem (g : St n R) : stab n R g ∈ vdkInjCoset_rowStab n R := by
  have hg : g ∈ (vdkInjCoset_rowStab n R).comap (stab n R) := by
    refine PresentedGroup.generated_by _ _ ?_ g
    rintro ⟨i, j, hij, a⟩
    exact Subgroup.mem_comap.mpr (vdkInjCoset_stab_x_mem i j hij a)
  exact Subgroup.mem_comap.mp hg

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCoset_stab_mem

/-- The column product `colVec v = ∏ᵢ x_{i,last}(vᵢ)` fixes `e_last`. -/
theorem vdkInjCoset_colVec_mem (v : Fin n → R) : colVec v ∈ vdkInjCoset_rowStab n R := by
  have key : ∀ s : Finset (Fin n),
      colVec (∑ i ∈ s, (Pi.single i (v i) : Fin n → R)) ∈ vdkInjCoset_rowStab n R := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, colVec_zero]
      exact one_mem _
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, colVec_add, vdkRow_colVec_single]
      exact mul_mem (vdkInjCoset_colRoot_mem a (v a)) ih
  have h := key Finset.univ
  rwa [Finset.univ_sum_single] at h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCoset_colVec_mem

/-- **`P ≤ rowStab`**: the parabolic image `colVec v · stab g` fixes `e_last`. -/
theorem vdkInjCoset_rowPar_le : vdkRowParSubgroup n R ≤ vdkInjCoset_rowStab n R := by
  intro h hh
  obtain ⟨⟨v, g⟩, rfl⟩ := (mem_vdkRowParSubgroup h).mp hh
  rw [vdkRowPar_apply]
  exact mul_mem (vdkInjCoset_colVec_mem v) (vdkInjCoset_stab_mem g)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCoset_rowPar_le

/-- A `K₂` element has matrix `1`. -/
theorem vdkInjCoset_projectionMatrix_of_mem_K2 {m : ℕ} {g : St m R} (hg : g ∈ K2n m R) :
    projectionMatrix g = 1 := by
  simp only [projectionMatrix, (mem_K2_iff g).mp hg, Subgroup.coe_one, Units.val_one]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCoset_projectionMatrix_of_mem_K2

/-- **`K₂(n+1, R) ≤ rowStab`**. -/
theorem vdkInjCoset_K2_le_rowStab : K2n (n + 1) R ≤ vdkInjCoset_rowStab n R := by
  intro g hg
  rw [vdkInjCoset_mem_rowStab, vdkInjCoset_projectionMatrix_of_mem_K2 hg, Matrix.vecMul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCoset_K2_le_rowStab

end GroupApproximation.BooneHigman.Metabelian.ElemFP
