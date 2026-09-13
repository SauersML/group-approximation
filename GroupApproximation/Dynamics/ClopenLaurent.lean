import GroupApproximation.Dynamics.ClopenCrossedProduct
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# Laurent expansions in `R_X`

`non_mf_groups_exist.tex`, `\label{sec:chain-core}`, tex 1351–1354:

> Here $\operatorname{LC}$ denotes locally constant functions and the crossed product is
> algebraic: its elements have unique finite Laurent expansions $\sum_j f_j u^j$.  The powers of
> $u$ remain formal even if $T$ has finite order.

* `laurentSum T k f = ∑_j f_j u^j` for a finitely supported family `f : ℤ →₀ LC(X, k)`;
* `laurentSum_coeff`: the coefficient of `laurentSum T k f` at `ofAdd i` is `f i`;
* `laurentCoeff` and `laurentSum_laurentCoeff`: every element of `R_X` is a Laurent sum;
* `existsUnique_laurentSum`: every element of `R_X` is `laurentSum T k f` for exactly one `f`;
* `unit_zpow_injective`: `j ↦ u ^ j` is injective when `X` is nonempty and `1 ≠ 0` in `k`;
* closed endpoints `printedLaurentExpansionsUnique` (tex 1352–1353) and `printedPowersFormal`
  (tex 1353–1354).
-/

namespace GroupApproximation

namespace ClopenCrossedProduct

open Multiplicative (ofAdd toAdd)

variable {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X) (k : Type*) [Ring k]

/-- The Laurent sum `∑_j f_j u^j` of a finitely supported family `f : ℤ →₀ LC(X, k)`. -/
noncomputable def laurentSum (f : ℤ →₀ LocallyConstant X k) : ClopenCrossedProduct T k :=
  f.sum fun j c =>
    coeff T k c * ((unit T k ^ j : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k)

/-- `f u^j` is the monomial `single (ofAdd j) f`. -/
theorem coeff_mul_unit_zpow (c : LocallyConstant X k) (j : ℤ) :
    coeff T k c * ((unit T k ^ j : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k) =
      SkewMonoidAlgebra.single (ofAdd j) (ClopenCoeff.of T k c) := by
  have hu : ((unit T k ^ j : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k) =
      SkewMonoidAlgebra.single (ofAdd j) 1 :=
    Pestov91.CrossedProduct.val_unit_zpow j
  rw [hu, coeff_apply, Pestov91.CrossedProduct.C_mul_single, mul_one]

theorem laurentSum_single (j : ℤ) (c : LocallyConstant X k) :
    laurentSum T k (Finsupp.single j c) =
      coeff T k c * ((unit T k ^ j : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k) :=
  Finsupp.sum_single_index (by simp only [map_zero, zero_mul])

/-- The coefficient of `∑_j f_j u^j` at `u^i` is `f_i`. -/
theorem laurentSum_coeff (f : ℤ →₀ LocallyConstant X k) (i : ℤ) :
    SkewMonoidAlgebra.coeff (laurentSum T k f) (ofAdd i) = ClopenCoeff.of T k (f i) := by
  classical
  rw [← SkewMonoidAlgebra.coeffAddEquiv_apply, laurentSum, Finsupp.sum, _root_.map_sum,
    Finsupp.finsetSum_apply, Finset.sum_eq_single i]
  · rw [coeff_mul_unit_zpow, SkewMonoidAlgebra.coeffAddEquiv_apply, SkewMonoidAlgebra.coeff_single,
      Finsupp.single_eq_same]
  · intro j _ hji
    rw [coeff_mul_unit_zpow, SkewMonoidAlgebra.coeffAddEquiv_apply, SkewMonoidAlgebra.coeff_single,
      Finsupp.single_apply, if_neg (fun e : ofAdd j = ofAdd i => hji (ofAdd.injective e))]
  · intro hi
    simp only [Finsupp.notMem_support_iff.1 hi, map_zero, zero_mul, Finsupp.coe_zero,
      Pi.zero_apply]

/-- Laurent expansions are unique. -/
theorem laurentSum_injective : Function.Injective (laurentSum T k) := fun f g hfg =>
  Finsupp.ext fun i => (ClopenCoeff.of T k).injective <| by
    rw [← laurentSum_coeff T k f i, ← laurentSum_coeff T k g i, hfg]

/-- The Laurent coefficients `i ↦ x_i` of `x ∈ R_X`. -/
noncomputable def laurentCoeff (x : ClopenCrossedProduct T k) : ℤ →₀ LocallyConstant X k :=
  Finsupp.onFinset ((SkewMonoidAlgebra.support x).map toAdd.toEmbedding)
    (fun i => (ClopenCoeff.of T k).symm (SkewMonoidAlgebra.coeff x (ofAdd i))) fun i hi => by
      have h : SkewMonoidAlgebra.coeff x (ofAdd i) ≠ 0 := fun h0 => hi (by simp only [h0, map_zero])
      exact Finset.mem_map_of_mem toAdd.toEmbedding (SkewMonoidAlgebra.mem_support_iff.2 h)

/-- Every element of `R_X` is the Laurent sum of its coefficients. -/
theorem laurentSum_laurentCoeff (x : ClopenCrossedProduct T k) :
    laurentSum T k (laurentCoeff T k x) = x :=
  SkewMonoidAlgebra.ext fun a => by
    rw [← ofAdd_toAdd a, laurentSum_coeff, laurentCoeff, Finsupp.onFinset_apply]
    exact (ClopenCoeff.of T k).apply_symm_apply _

theorem existsUnique_laurentSum (x : ClopenCrossedProduct T k) :
    ∃! f : ℤ →₀ LocallyConstant X k, x = laurentSum T k f :=
  ⟨laurentCoeff T k x, (laurentSum_laurentCoeff T k x).symm,
    fun g (hg : x = laurentSum T k g) =>
      laurentSum_injective T k (hg.symm.trans (laurentSum_laurentCoeff T k x).symm)⟩

/-- The powers of `u` are pairwise distinct, whatever the order of `T`. -/
theorem unit_zpow_injective [Nonempty X] [Nontrivial k] :
    Function.Injective fun j : ℤ =>
      ((unit T k ^ j : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k) := by
  intro i j hij
  have h1 : (1 : LocallyConstant X k) ≠ 0 := fun h => by
    simpa using DFunLike.congr_fun h (Classical.arbitrary X)
  have hs : Finsupp.single i (1 : LocallyConstant X k) = Finsupp.single j 1 := by
    apply laurentSum_injective T k
    simpa only [laurentSum_single, map_one, one_mul] using hij
  exact Finsupp.single_left_injective h1 hs

/-- **tex 1351–1353**: "the crossed product is algebraic: its elements have unique finite Laurent
expansions $\sum_j f_j u^j$."  Every element of `R_X` is `∑_j f_j u^j` for exactly one finitely
supported family `f : ℤ →₀ LC(X, k)`.

The statement holds for every topological space `X`, homeomorphism `T` and ring `k`; the printed
hypotheses on `X` and `k` are not used. -/
def PrintedLaurentExpansionsUnique : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (T : X ≃ₜ X) (k : Type) [Ring k]
    (x : ClopenCrossedProduct T k), ∃! f : ℤ →₀ LocallyConstant X k,
      x = f.sum fun j c =>
        coeff T k c * ((unit T k ^ j : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k)

theorem printedLaurentExpansionsUnique : PrintedLaurentExpansionsUnique := by
  intro _ _ T k _ x
  exact existsUnique_laurentSum T k x

/-- **tex 1353–1354**: "The powers of $u$ remain formal even if $T$ has finite order."  For every
homeomorphism `T`, including those with `T ^ n = 1`, the powers `u ^ j` (`j ∈ ℤ`) are pairwise
distinct.

Of the printed hypotheses only `X ≠ ∅` and `1 ≠ 0` in `k` are used. -/
def PrintedPowersFormal : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [Nonempty X] (T : X ≃ₜ X) (k : Type) [Ring k] [Nontrivial k],
    Function.Injective fun j : ℤ =>
      ((unit T k ^ j : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k)

theorem printedPowersFormal : PrintedPowersFormal := by
  intro _ _ _ T k _ _
  exact unit_zpow_injective T k

end ClopenCrossedProduct

end GroupApproximation

open GroupApproximation

#audit_closed_axioms GroupApproximation.ClopenCrossedProduct.printedLaurentExpansionsUnique
#audit_closed_axioms GroupApproximation.ClopenCrossedProduct.printedPowersFormal
