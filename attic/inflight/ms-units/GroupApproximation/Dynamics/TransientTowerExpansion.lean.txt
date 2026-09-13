import GroupApproximation.Dynamics.TransientTowerFamily
import GroupApproximation.Dynamics.ClopenCrossedProductAlgebra
import GroupApproximation.Meta.AxiomGuard

/-!
# The prescribed elements are combinations of tower units

`non_mf_groups_exist.tex`, `\label{lem:transient-matrices}`, proof, tex 1492–1493 and 1512–1513:

> Express a prescribed finite subset of $I$ as linear combinations of characteristic functions of
> compact clopen partial shift graphs.  [...]  The product of these finitely many matrix algebras
> contains the prescribed elements, proving local matriciality.

Over the cells of `Dynamics/TransientTowerFamily`, a monomial `c u^j` of `R_X` is a `k`-combination
of the tower units when
* `j` is one of the step exponents `E`;
* `c` vanishes off `C`, and off the points `z` with `T^{-j} z ∈ C`;
* `c ∘ T^d` is constant on each cell, for every exponent `d` of the cell (the refinement "according
  to all original coefficient values");
* every representative of `C` lies in some cell.

* `single_eq_sum_transientTower`: the monomial `c u^j` in tower units.
* `exists_matrix_eq_sum_transientTower`: a whole element, the form the matrix-unit criterion takes.
-/

namespace GroupApproximation
namespace ClopenCrossedProduct

open ChainCore
open Multiplicative (ofAdd toAdd)

section Expansion

variable {X : Type*} [TopologicalSpace X] {T : X ≃ₜ X} (k : Type*) [CommRing k]
  {C : Set X} {E : Finset ℤ} {m M : ℕ} {cell : Fin M → Set X} {S : Fin M → Finset ℤ}

theorem transientCoeff_symm_smul_apply (c : k) (f : ClopenCoeff T k) (z : X) :
    (ClopenCoeff.of T k).symm (c • f) z = c * (ClopenCoeff.of T k).symm f z := by
  rw [Algebra.smul_def, map_mul, LocallyConstant.mul_apply]
  rfl

theorem transientCoeff_symm_sum_apply {ι : Type*} (s : Finset ι) (f : ι → ClopenCoeff T k)
    (z : X) :
    (ClopenCoeff.of T k).symm (∑ i ∈ s, f i) z = ∑ i ∈ s, (ClopenCoeff.of T k).symm (f i) z := by
  rw [map_sum]
  exact map_sum (LocallyConstant.evalRingHom z) (fun i => (ClopenCoeff.of T k).symm (f i)) s

theorem transientSingle_sum (j : Multiplicative ℤ) {ι : Type*} (s : Finset ι)
    (f : ι → ClopenCoeff T k) :
    SkewMonoidAlgebra.single j (∑ i ∈ s, f i) = ∑ i ∈ s, SkewMonoidAlgebra.single j (f i) :=
  map_sum (AddMonoidHom.mk' (SkewMonoidAlgebra.single j) (SkewMonoidAlgebra.single_add j)) f s

variable (hcell : ∀ a, IsClopen (cell a))

theorem transientTowerCoeff_apply_of_mem {a : Fin M} {i : Fin (S a).card} {z : X}
    (hz : z ∈ transientTowerLevel T cell S a i) :
    (ClopenCoeff.of T k).symm (transientTowerCoeff T k cell S hcell a i) z = 1 := by
  show LocallyConstant.charFn k (isClopen_transientTowerLevel T cell S hcell a i) z = 1
  rw [LocallyConstant.coe_charFn, Set.indicator_of_mem hz, Pi.one_apply]

theorem transientTowerCoeff_apply_of_not_mem {a : Fin M} {i : Fin (S a).card} {z : X}
    (hz : z ∉ transientTowerLevel T cell S a i) :
    (ClopenCoeff.of T k).symm (transientTowerCoeff T k cell S hcell a i) z = 0 := by
  show LocallyConstant.charFn k (isClopen_transientTowerLevel T cell S hcell a i) z = 0
  exact charFn_apply_eq_zero _ hz

variable (T S) in
/-- The coefficient matrix of the monomial `c u^j` over cell `a`: the arrow from level `i'` to
level `i` carries the value of `c` on level `i` exactly when `d_i - d_{i'} = j`. -/
noncomputable def transientTowerCoeffMatrix (rep : Fin M → X) (j : ℤ) (c : LocallyConstant X k)
    (a : Fin M) : Matrix (Fin (S a).card) (Fin (S a).card) k :=
  fun i i' => if transientTowerExp S a i - transientTowerExp S a i' = j then
    c ((T ^ transientTowerExp S a i) (rep a)) else 0

theorem transientTowerSmulUnit_eq_single (rep : Fin M → X) (j : ℤ) (c : LocallyConstant X k)
    (a : Fin M) (i i' : Fin (S a).card) :
    transientTowerCoeffMatrix T k S rep j c a i i' •
        Pestov91.CrossedProduct.towerUnit (transientTowerCoeff T k cell S hcell)
          (transientTowerExp S) a i i' =
      SkewMonoidAlgebra.single (ofAdd j)
        (transientTowerCoeffMatrix T k S rep j c a i i' • transientTowerCoeff T k cell S hcell a i) := by
  simp only [transientTowerCoeffMatrix]
  split_ifs with h
  · rw [Pestov91.CrossedProduct.towerUnit, SkewMonoidAlgebra.smul_single, h]
  · rw [zero_smul, zero_smul, SkewMonoidAlgebra.single_zero]

theorem transientTowerSum_smulUnit_eq_single (rep : Fin M → X) (j : ℤ)
    (c : LocallyConstant X k) :
    ∑ a, ∑ i, ∑ i', transientTowerCoeffMatrix T k S rep j c a i i' •
        Pestov91.CrossedProduct.towerUnit (transientTowerCoeff T k cell S hcell)
          (transientTowerExp S) a i i' =
      SkewMonoidAlgebra.single (ofAdd j)
        (∑ a, ∑ i, ∑ i', transientTowerCoeffMatrix T k S rep j c a i i' •
          transientTowerCoeff T k cell S hcell a i) := by
  simp only [transientTowerSmulUnit_eq_single k hcell rep j c, transientSingle_sum]

/-- **The coefficient of the combination at a point** is the value of `c` there. -/
theorem transientTowerSum_apply (hm : ExponentBound T C m)
    (hsub : ∀ a, cell a ⊆ baseCell T C E m (S a))
    (hdisj : ∀ a b, a ≠ b → Disjoint (cell a) (cell b))
    (hcover : ∀ y ∈ baseSet T C E m, ∃ a, y ∈ cell a) (rep : Fin M → X)
    (hrep : ∀ a, rep a ∈ cell a) {j : ℤ} (hj : j ∈ E) (c : LocallyConstant X k)
    (hsupp : ∀ z, c z ≠ 0 → z ∈ C ∧ (T ^ (-j)) z ∈ C)
    (hconst : ∀ a, ∀ d ∈ S a, ∀ y ∈ cell a, ∀ y' ∈ cell a, c ((T ^ d) y) = c ((T ^ d) y'))
    (z : X) :
    (ClopenCoeff.of T k).symm (∑ a, ∑ i, ∑ i', transientTowerCoeffMatrix T k S rep j c a i i' •
      transientTowerCoeff T k cell S hcell a i) z = c z := by
  simp only [transientCoeff_symm_sum_apply, transientCoeff_symm_smul_apply]
  by_cases hcz : c z = 0
  · rw [hcz]
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun i _ =>
      Finset.sum_eq_zero fun i' _ => ?_
    by_cases hz : z ∈ transientTowerLevel T cell S a i
    · obtain ⟨y, hy, rfl⟩ := hz
      simp only [transientTowerCoeffMatrix]
      split_ifs
      · rw [hconst a _ (transientTowerExp_mem S a i) (rep a) (hrep a) y hy, hcz, zero_mul]
      · rw [zero_mul]
    · rw [transientTowerCoeff_apply_of_not_mem k hcell hz, mul_zero]
  · obtain ⟨hzC, hjC⟩ := hsupp z hcz
    obtain ⟨y, d, hy, hd, rfl⟩ := exists_mem_baseCell_level (E := E) hm hzC
    obtain ⟨a, hya⟩ := hcover y hy.1
    have hSa : reachableExponents T C E (m - 1) y = S a := (hsub a hya).2
    have hdS : d ∈ S a := by rw [← hSa]; exact hd
    obtain ⟨i, hi⟩ := exists_transientTowerExp_eq S hdS
    have hdj : d - j ∈ S a := by
      rw [← hSa, ← reachableExponents_eq_of_le hm y (r := m - 1 + 1) (by omega)]
      refine mem_reachableExponents_succ.2 ⟨Or.inr ⟨d, hd, -j, ?_, by ring⟩, ?_⟩
      · exact mem_stepExponents.2 (Or.inr (by rwa [neg_neg]))
      · rwa [Dynamics.zpow_apply_zpow_apply, show -j + d = d - j by ring] at hjC
    obtain ⟨i', hi'⟩ := exists_transientTowerExp_eq S hdj
    have hzL : (T ^ d) y ∈ transientTowerLevel T cell S a i := ⟨y, hya, by rw [hi]⟩
    have h1 : ∀ a₁, a₁ ≠ a → ∑ i₁, ∑ i₂, transientTowerCoeffMatrix T k S rep j c a₁ i₁ i₂ *
        (ClopenCoeff.of T k).symm (transientTowerCoeff T k cell S hcell a₁ i₁) ((T ^ d) y) = 0 := by
      intro a₁ ha₁
      refine Finset.sum_eq_zero fun i₁ _ => Finset.sum_eq_zero fun i₂ _ => ?_
      rw [transientTowerCoeff_apply_of_not_mem k hcell (Set.disjoint_right.1
        (disjoint_transientTowerLevel hm hsub hdisj i₁ i (Or.inl ha₁)) hzL), mul_zero]
    have h2 : ∀ i₁, i₁ ≠ i → ∑ i₂, transientTowerCoeffMatrix T k S rep j c a i₁ i₂ *
        (ClopenCoeff.of T k).symm (transientTowerCoeff T k cell S hcell a i₁) ((T ^ d) y) = 0 := by
      intro i₁ hi₁
      refine Finset.sum_eq_zero fun i₂ _ => ?_
      rw [transientTowerCoeff_apply_of_not_mem k hcell (Set.disjoint_right.1
        (disjoint_transientTowerLevel hm hsub hdisj i₁ i
          (Or.inr fun h => hi₁ (transientTowerExp_injective S a h))) hzL), mul_zero]
    have h3 : ∀ i₂, i₂ ≠ i' → transientTowerCoeffMatrix T k S rep j c a i i₂ *
        (ClopenCoeff.of T k).symm (transientTowerCoeff T k cell S hcell a i) ((T ^ d) y) = 0 := by
      intro i₂ hi₂
      have hne : transientTowerExp S a i - transientTowerExp S a i₂ ≠ j := by
        intro h
        apply hi₂
        apply transientTowerExp_injective S a
        rw [hi']
        omega
      simp only [transientTowerCoeffMatrix, if_neg hne, zero_mul]
    rw [Fintype.sum_eq_single a h1, Fintype.sum_eq_single i h2, Fintype.sum_eq_single i' h3]
    simp only [transientTowerCoeffMatrix]
    rw [if_pos (by rw [hi, hi']; ring), transientTowerCoeff_apply_of_mem k hcell hzL, mul_one,
      hconst a _ (transientTowerExp_mem S a i) (rep a) (hrep a) y hya, hi]

/-- **A monomial `c u^j` is a combination of tower units.** -/
theorem single_eq_sum_transientTower (hm : ExponentBound T C m)
    (hsub : ∀ a, cell a ⊆ baseCell T C E m (S a))
    (hdisj : ∀ a b, a ≠ b → Disjoint (cell a) (cell b))
    (hcover : ∀ y ∈ baseSet T C E m, ∃ a, y ∈ cell a) (rep : Fin M → X)
    (hrep : ∀ a, rep a ∈ cell a) {j : ℤ} (hj : j ∈ E) (c : LocallyConstant X k)
    (hsupp : ∀ z, c z ≠ 0 → z ∈ C ∧ (T ^ (-j)) z ∈ C)
    (hconst : ∀ a, ∀ d ∈ S a, ∀ y ∈ cell a, ∀ y' ∈ cell a, c ((T ^ d) y) = c ((T ^ d) y')) :
    SkewMonoidAlgebra.single (ofAdd j) (ClopenCoeff.of T k c) =
      ∑ a, ∑ i, ∑ i', transientTowerCoeffMatrix T k S rep j c a i i' •
        Pestov91.CrossedProduct.towerUnit (transientTowerCoeff T k cell S hcell)
          (transientTowerExp S) a i i' := by
  rw [transientTowerSum_smulUnit_eq_single k hcell rep j c]
  congr 1
  apply (ClopenCoeff.of T k).symm.injective
  rw [RingEquiv.symm_apply_apply]
  exact LocallyConstant.ext fun z =>
    (transientTowerSum_apply k hcell hm hsub hdisj hcover rep hrep hj c hsupp hconst z).symm

/-- **A whole element is a combination of tower units**, in the form of the matrix-unit criterion
`isLocallyMatricialIn_of_forall_exists_family`. -/
theorem exists_matrix_eq_sum_transientTower (hm : ExponentBound T C m)
    (hsub : ∀ a, cell a ⊆ baseCell T C E m (S a))
    (hdisj : ∀ a b, a ≠ b → Disjoint (cell a) (cell b))
    (hcover : ∀ y ∈ baseSet T C E m, ∃ a, y ∈ cell a) (rep : Fin M → X)
    (hrep : ∀ a, rep a ∈ cell a) (x : ClopenCrossedProduct T k)
    (hx : ∀ g ∈ SkewMonoidAlgebra.support x, toAdd g ∈ E ∧
      ∀ z, (ClopenCoeff.of T k).symm (SkewMonoidAlgebra.coeff x g) z ≠ 0 → z ∈ C ∧ (T ^ (-toAdd g)) z ∈ C)
    (hconst : ∀ g ∈ SkewMonoidAlgebra.support x, ∀ a, ∀ d ∈ S a, ∀ y ∈ cell a, ∀ y' ∈ cell a,
      (ClopenCoeff.of T k).symm (SkewMonoidAlgebra.coeff x g) ((T ^ d) y) =
        (ClopenCoeff.of T k).symm (SkewMonoidAlgebra.coeff x g) ((T ^ d) y')) :
    ∃ c : ∀ a : Fin M, Matrix (Fin (S a).card) (Fin (S a).card) k,
      x = ∑ a, ∑ i, ∑ i', c a i i' •
        Pestov91.CrossedProduct.towerUnit (transientTowerCoeff T k cell S hcell)
          (transientTowerExp S) a i i' := by
  refine ⟨fun a i i' => ∑ g ∈ SkewMonoidAlgebra.support x, transientTowerCoeffMatrix T k S rep (toAdd g)
    ((ClopenCoeff.of T k).symm (SkewMonoidAlgebra.coeff x g)) a i i', ?_⟩
  calc x = ∑ g ∈ SkewMonoidAlgebra.support x, SkewMonoidAlgebra.single g (SkewMonoidAlgebra.coeff x g) :=
        ((SkewMonoidAlgebra.sum_def' x SkewMonoidAlgebra.single).symm.trans
          (SkewMonoidAlgebra.sum_single x)).symm
    _ = ∑ g ∈ SkewMonoidAlgebra.support x, ∑ a, ∑ i, ∑ i', transientTowerCoeffMatrix T k S rep (toAdd g)
          ((ClopenCoeff.of T k).symm (SkewMonoidAlgebra.coeff x g)) a i i' •
          Pestov91.CrossedProduct.towerUnit (transientTowerCoeff T k cell S hcell)
            (transientTowerExp S) a i i' := by
        refine Finset.sum_congr rfl fun g hg => ?_
        have h := single_eq_sum_transientTower k hcell hm hsub hdisj hcover rep hrep (hx g hg).1
          ((ClopenCoeff.of T k).symm (SkewMonoidAlgebra.coeff x g)) (hx g hg).2 (hconst g hg)
        rw [RingEquiv.apply_symm_apply] at h
        exact h
    _ = _ := by
        simp only [Finset.sum_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]

end Expansion

end ClopenCrossedProduct
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.ClopenCrossedProduct.transientTowerSum_apply
#audit_axioms GroupApproximation.ClopenCrossedProduct.single_eq_sum_transientTower
#audit_axioms GroupApproximation.ClopenCrossedProduct.exists_matrix_eq_sum_transientTower
