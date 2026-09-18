import GroupApproximation.BooneHigman.Metabelian.SuslinNormalTransvection
import GroupApproximation.Meta.AxiomGuard

/-!
# Suslin normality, part 2: orthogonal rank-one transvections

Lane `bh-met-39b`.  Continuing `SuslinNormalTransvection`:

* `suslinNormal_inE_of_pointwise`: `1 + x yᵀ ∈ E_ι(A)` when `x m * y m = 0` for all `m`;
* `suslinNormal_inE_of_vanish`: `1 + x yᵀ ∈ E_ι(A)` when `yᵀ x = 0` and `x k = y k = 0`
  for one index `k`, via the commutator `[1 + x e_kᵀ, 1 + e_k yᵀ] = 1 + x yᵀ`;
* `suslinNormal_inE_of_dot_zero`: `1 + x yᵀ ∈ E_ι(A)` when `yᵀ x = 0` and `y k = 0` for one
  index `k` (split off the `k`-th coordinate of `x`).
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

section Orthogonal

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A]

/-- `1 + (c e_k) yᵀ ∈ E_ι(A)` when `c * y k = 0`. -/
theorem suslinNormal_inE_single_left (k : ι) (c : A) (y : ι → A) (hy : c * y k = 0) :
    SuslinNormalInE ι A (1 + Matrix.vecMulVec (Pi.single k c) y) := by
  have key : ∀ t : Finset ι, ∀ z : ι → A, c * z k = 0 → (∀ m, m ∉ t → z m = 0) →
      SuslinNormalInE ι A (1 + Matrix.vecMulVec (Pi.single k c) z) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro z _ hz
      have hz0 : z = 0 := funext fun m => hz m (Finset.notMem_empty m)
      rw [hz0, Matrix.vecMulVec_zero, add_zero]
      exact suslinNormal_inE_one
    | insert l t _ ih =>
      intro z hkz hz
      have hupd : c * Function.update z l 0 k = 0 := by
        by_cases hkl : k = l
        · rw [hkl, Function.update_self, mul_zero]
        · rw [Function.update_of_ne hkl]
          exact hkz
      rw [suslinNormal_update_add_single z l, Matrix.vecMulVec_add]
      refine suslinNormal_inE_add (ih _ hupd (suslinNormal_update_support hz))
        (suslinNormal_inE_single_single k l c (z l) ?_) ?_
      · intro hkl
        rw [← hkl]
        exact hkz
      · apply suslinNormal_vecMulVec_mul_of_dot
        rw [dotProduct_single, mul_comm]
        exact hupd
  exact key Finset.univ y hy (fun m hm => absurd (Finset.mem_univ m) hm)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinNormal_inE_single_left

/-- **Pointwise orthogonal supports.**  `1 + x yᵀ ∈ E_ι(A)` when `x m * y m = 0` for all `m`. -/
theorem suslinNormal_inE_of_pointwise (x y : ι → A) (hxy : ∀ m, x m * y m = 0) :
    SuslinNormalInE ι A (1 + Matrix.vecMulVec x y) := by
  have key : ∀ s : Finset ι, ∀ z : ι → A, (∀ m, z m * y m = 0) → (∀ m, m ∉ s → z m = 0) →
      SuslinNormalInE ι A (1 + Matrix.vecMulVec z y) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro z _ hz
      have hz0 : z = 0 := funext fun m => hz m (Finset.notMem_empty m)
      rw [hz0, Matrix.zero_vecMulVec, add_zero]
      exact suslinNormal_inE_one
    | insert k s _ ih =>
      intro z hzy hz
      have hupd : ∀ m, Function.update z k 0 m * y m = 0 := by
        intro m
        by_cases hmk : m = k
        · rw [hmk, Function.update_self, zero_mul]
        · rw [Function.update_of_ne hmk]
          exact hzy m
      rw [suslinNormal_update_add_single z k, Matrix.add_vecMulVec]
      refine suslinNormal_inE_add (ih _ hupd (suslinNormal_update_support hz))
        (suslinNormal_inE_single_left k (z k) y (hzy k)) ?_
      apply suslinNormal_vecMulVec_mul_of_dot
      rw [dotProduct_single, mul_comm]
      exact hzy k
  exact key Finset.univ x hxy (fun m hm => absurd (Finset.mem_univ m) hm)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinNormal_inE_of_pointwise

/-- **The commutator step.**  If `x k = 0`, `y k = 0` and `yᵀ x = 0`, then
`(1 + x e_kᵀ)(1 + e_k yᵀ)(1 - x e_kᵀ)(1 - e_k yᵀ) = 1 + x yᵀ` is elementary. -/
theorem suslinNormal_inE_of_vanish {x y : ι → A} {k : ι} (hxk : x k = 0) (hyk : y k = 0)
    (hyx : y ⬝ᵥ x = 0) : SuslinNormalInE ι A (1 + Matrix.vecMulVec x y) := by
  have hex : Pi.single k (1 : A) ⬝ᵥ x = 0 := by rw [single_dotProduct, hxk, mul_zero]
  have hye : y ⬝ᵥ Pi.single k (1 : A) = 0 := by rw [dotProduct_single, hyk, zero_mul]
  have hee : Pi.single k (1 : A) ⬝ᵥ Pi.single k (1 : A) = 1 := by
    rw [single_dotProduct, Pi.single_eq_same, one_mul]
  have hX : SuslinNormalInE ι A (1 + Matrix.vecMulVec x (Pi.single k (1 : A))) := by
    apply suslinNormal_inE_of_pointwise
    intro m
    by_cases hmk : m = k
    · rw [hmk, hxk, zero_mul]
    · rw [Pi.single_eq_of_ne hmk, mul_zero]
  have hY : SuslinNormalInE ι A (1 + Matrix.vecMulVec (Pi.single k (1 : A)) y) := by
    apply suslinNormal_inE_of_pointwise
    intro m
    by_cases hmk : m = k
    · rw [hmk, hyk, mul_zero]
    · rw [Pi.single_eq_of_ne hmk, zero_mul]
  have hXX : Matrix.vecMulVec x (Pi.single k (1 : A)) *
      Matrix.vecMulVec x (Pi.single k (1 : A)) = 0 := suslinNormal_vecMulVec_mul_of_dot hex
  have hYY : Matrix.vecMulVec (Pi.single k (1 : A)) y *
      Matrix.vecMulVec (Pi.single k (1 : A)) y = 0 := suslinNormal_vecMulVec_mul_of_dot hye
  have hYX : Matrix.vecMulVec (Pi.single k (1 : A)) y *
      Matrix.vecMulVec x (Pi.single k (1 : A)) = 0 := suslinNormal_vecMulVec_mul_of_dot hyx
  have hXY : Matrix.vecMulVec x (Pi.single k (1 : A)) *
      Matrix.vecMulVec (Pi.single k (1 : A)) y = Matrix.vecMulVec x y := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hee, one_smul]
  have hXZ : Matrix.vecMulVec x (Pi.single k (1 : A)) * Matrix.vecMulVec x y = 0 :=
    suslinNormal_vecMulVec_mul_of_dot hex
  have hZX : Matrix.vecMulVec x y * Matrix.vecMulVec x (Pi.single k (1 : A)) = 0 :=
    suslinNormal_vecMulVec_mul_of_dot hyx
  have hYZ : Matrix.vecMulVec (Pi.single k (1 : A)) y * Matrix.vecMulVec x y = 0 :=
    suslinNormal_vecMulVec_mul_of_dot hyx
  have hZY : Matrix.vecMulVec x y * Matrix.vecMulVec (Pi.single k (1 : A)) y = 0 :=
    suslinNormal_vecMulVec_mul_of_dot hye
  have hZZ : Matrix.vecMulVec x y * Matrix.vecMulVec x y = 0 :=
    suslinNormal_vecMulVec_mul_of_dot hyx
  have hprod : (1 + Matrix.vecMulVec x (Pi.single k (1 : A))) *
      (1 + Matrix.vecMulVec (Pi.single k (1 : A)) y) *
      (1 - Matrix.vecMulVec x (Pi.single k (1 : A))) *
      (1 - Matrix.vecMulVec (Pi.single k (1 : A)) y) = 1 + Matrix.vecMulVec x y := by
    noncomm_ring [hXX, hYY, hYX, hXY, hXZ, hZX, hYZ, hZY, hZZ]
  rw [← hprod]
  exact suslinNormal_inE_mul (suslinNormal_inE_mul (suslinNormal_inE_mul hX hY)
    (suslinNormal_inE_sub_of_sq hXX hX)) (suslinNormal_inE_sub_of_sq hYY hY)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinNormal_inE_of_vanish

/-- `1 + x yᵀ ∈ E_ι(A)` when `yᵀ x = 0` and `y` vanishes at one index `k`. -/
theorem suslinNormal_inE_of_dot_zero {x y : ι → A} {k : ι} (hyk : y k = 0)
    (hyx : y ⬝ᵥ x = 0) : SuslinNormalInE ι A (1 + Matrix.vecMulVec x y) := by
  have hsplit := suslinNormal_update_add_single x k
  have hyk' : y ⬝ᵥ Pi.single k (x k) = 0 := by rw [dotProduct_single, hyk, zero_mul]
  have hyx' : y ⬝ᵥ Function.update x k 0 = 0 := by
    have h := hyx
    rw [hsplit, dotProduct_add, hyk', add_zero] at h
    exact h
  rw [hsplit, Matrix.add_vecMulVec]
  refine suslinNormal_inE_add
    (suslinNormal_inE_of_vanish (Function.update_self k (0 : A) x) hyk hyx')
    (suslinNormal_inE_of_pointwise _ _ ?_) (suslinNormal_vecMulVec_mul_of_dot hyk')
  intro m
  by_cases hmk : m = k
  · rw [hmk, hyk, mul_zero]
  · rw [Pi.single_eq_of_ne hmk, zero_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinNormal_inE_of_dot_zero

end Orthogonal

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
