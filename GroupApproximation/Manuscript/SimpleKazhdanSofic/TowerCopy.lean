import GroupApproximation.Manuscript.SimpleKazhdanSofic.TowerMatrixUnits
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basis

/-!
# The tower copy `ψ` of `M_{2w+1}(F_2)`

`simple_kazhdan_sofic_group.tex` at e80dcf20a, subsection "Simplicity":

> Index the coordinates of $\F_2^d$ by pairs $(p,a)$ with $1\le p\le3$ and $|a|\le w$. Then
> $\psi(E_{(p,a),(q,b)})=\epsilon_{ab}E_{pq}$ defines an injective multiplicative linear map
> $\psi\colon M_d(\F_2)\to M_3(R)$.

This module builds the block form of `ψ`: the constant matrices over `W` give a copy of
`M_{2m+1}(F_2)` inside `R_X`, and `ψ` is its entrywise extension to `M_3`.

* `towerHom hlev hWU hW : M_{2m+1}(F_2) →ₙ+* R_X`, `M ↦ ∑_{a,b} M_{ab} ε_{ab}`, the coefficient
  `M_{ab} ∈ F_2` acting through `ZMod.val`;
* `towerHom_single`: `ψ(E_{ab}) = ε_{ab}`;
* `towerHom_one`: the local identity is the tower unit `∑_a ε_{aa}`;
* `towerE_mul_towerHom_mul_towerE`: `ε_{aa} ψ(M) ε_{bb} = M_{ab} ε_{ab}`;
* `towerHom_injective` for nonempty `W`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

open ClopenCrossedProduct

variable {X : Type*} [TopologicalSpace X] {T : X ≃ₜ X}

/-- `1 + 1 = 0` in `R_X` over `F_2`. -/
theorem one_add_one_eq_zero : (1 : ClopenCrossedProduct T (ZMod 2)) + 1 = 0 := by
  have h : (1 : LocallyConstant X (ZMod 2)) + 1 = 0 := by
    ext x
    simp only [LocallyConstant.add_apply, LocallyConstant.one_apply, LocallyConstant.zero_apply]
    decide
  rw [← map_one (coeff T (ZMod 2)), ← map_add, h, map_zero]

theorem two_nsmul_eq_zero (y : ClopenCrossedProduct T (ZMod 2)) : 2 • y = 0 := by
  rw [two_nsmul, ← one_mul y, ← add_mul, one_add_one_eq_zero, zero_mul]

theorem mod_two_nsmul (n : ℕ) (y : ClopenCrossedProduct T (ZMod 2)) : (n % 2) • y = n • y := by
  conv_rhs => rw [← Nat.mod_add_div n 2]
  rw [add_nsmul, mul_nsmul, two_nsmul_eq_zero, nsmul_zero, add_zero]

theorem val_add_nsmul (x x' : ZMod 2) (y : ClopenCrossedProduct T (ZMod 2)) :
    (x + x').val • y = x.val • y + x'.val • y := by
  rw [ZMod.val_add, mod_two_nsmul, add_nsmul]

theorem val_mul_nsmul (x x' : ZMod 2) (y : ClopenCrossedProduct T (ZMod 2)) :
    (x * x').val • y = x.val • x'.val • y := by
  rw [ZMod.val_mul, mod_two_nsmul, mul_nsmul']

theorem nsmul_mul_nsmul (n n' : ℕ) (y y' : ClopenCrossedProduct T (ZMod 2)) :
    (n • y) * (n' • y') = (n * n') • (y * y') := by
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]

variable {m : ℕ} {U W : Set X}

theorem towerE_inter_self (hW : IsClopen W) (a b : Fin (2 * m + 1)) :
    towerE T (ZMod 2) m (hW.inter hW) a b = towerE T (ZMod 2) m hW a b := by
  unfold towerE
  congr 2
  exact charFn_congr _ _ (by rw [Set.inter_self])

/-- The additive map `M ↦ ∑_{a,b} M_{ab} ε_{ab}`. -/
noncomputable def towerAddHom (hW : IsClopen W) :
    Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) (ZMod 2) →+ ClopenCrossedProduct T (ZMod 2) where
  toFun M := ∑ a, ∑ b, (M a b).val • towerE T (ZMod 2) m hW a b
  map_zero' := by simp only [Matrix.zero_apply, ZMod.val_zero, zero_nsmul, Finset.sum_const_zero]
  map_add' M N := by simp only [Matrix.add_apply, val_add_nsmul, Finset.sum_add_distrib]

theorem towerAddHom_apply (hW : IsClopen W)
    (M : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) (ZMod 2)) :
    towerAddHom (T := T) hW M = ∑ a, ∑ b, (M a b).val • towerE T (ZMod 2) m hW a b := rfl

theorem towerAddHom_single (hW : IsClopen W) (a b : Fin (2 * m + 1)) (x : ZMod 2) :
    towerAddHom (T := T) hW (Matrix.single a b x) = x.val • towerE T (ZMod 2) m hW a b := by
  have h1 : ∀ a' : Fin (2 * m + 1), a' ≠ a →
      ∑ b', (Matrix.single a b x a' b').val • towerE T (ZMod 2) m hW a' b' = 0 := by
    intro a' ha'
    refine Finset.sum_eq_zero fun b' _ => ?_
    rw [Matrix.single_apply_of_row_ne ha'.symm, ZMod.val_zero, zero_nsmul]
  have h2 : ∀ b' : Fin (2 * m + 1), b' ≠ b →
      (Matrix.single a b x a b').val • towerE T (ZMod 2) m hW a b' = 0 := by
    intro b' hb'
    rw [Matrix.single_apply_of_col_ne a a hb'.symm x, ZMod.val_zero, zero_nsmul]
  rw [towerAddHom_apply, Fintype.sum_eq_single a h1, Fintype.sum_eq_single b h2,
    Matrix.single_apply_same]

theorem towerAddHom_single_mul_single (hlev : LevelsDisjoint T m U) (hWU : W ⊆ U)
    (hW : IsClopen W) (a b c d : Fin (2 * m + 1)) (x y : ZMod 2) :
    towerAddHom (T := T) hW (Matrix.single a b x * Matrix.single c d y) =
      towerAddHom hW (Matrix.single a b x) * towerAddHom hW (Matrix.single c d y) := by
  rw [towerAddHom_single, towerAddHom_single, nsmul_mul_nsmul,
    towerE_mul_towerE hlev hWU hWU hW hW]
  by_cases hbc : b = c
  · subst hbc
    rw [Matrix.single_mul_single_same, towerAddHom_single, if_pos rfl, towerE_inter_self,
      val_mul_nsmul, smul_smul]
  · rw [Matrix.single_mul_single_of_ne (h := hbc), map_zero, if_neg hbc, smul_zero]

/-- `ψ` is multiplicative: both sides are biadditive, and they agree on matrix units. -/
theorem towerAddHom_mul (hlev : LevelsDisjoint T m U) (hWU : W ⊆ U) (hW : IsClopen W)
    (M N : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) (ZMod 2)) :
    towerAddHom (T := T) hW (M * N) = towerAddHom hW M * towerAddHom hW N := by
  induction M using Matrix.induction_on' with
  | h_zero => rw [zero_mul, map_zero, zero_mul]
  | h_add p q hp hq => rw [add_mul, map_add, map_add, add_mul, hp, hq]
  | h_std_basis a b x =>
    induction N using Matrix.induction_on' with
    | h_zero => rw [mul_zero, map_zero, mul_zero]
    | h_add p q hp hq => rw [mul_add, map_add, map_add, mul_add, hp, hq]
    | h_std_basis c d y => exact towerAddHom_single_mul_single hlev hWU hW a b c d x y

/-- **The tower copy** `M_{2m+1}(F_2) →ₙ+* R_X`, `M ↦ ∑_{a,b} M_{ab} ε_{ab}`. -/
noncomputable def towerHom (hlev : LevelsDisjoint T m U) (hWU : W ⊆ U) (hW : IsClopen W) :
    Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) (ZMod 2) →ₙ+* ClopenCrossedProduct T (ZMod 2) where
  toFun := towerAddHom hW
  map_zero' := map_zero _
  map_add' := map_add _
  map_mul' := towerAddHom_mul hlev hWU hW

theorem towerHom_apply (hlev : LevelsDisjoint T m U) (hWU : W ⊆ U) (hW : IsClopen W)
    (M : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) (ZMod 2)) :
    towerHom hlev hWU hW M = ∑ a, ∑ b, (M a b).val • towerE T (ZMod 2) m hW a b := rfl

/-- `ψ(E_{ab}) = ε_{ab}`. -/
theorem towerHom_single (hlev : LevelsDisjoint T m U) (hWU : W ⊆ U) (hW : IsClopen W)
    (a b : Fin (2 * m + 1)) :
    towerHom hlev hWU hW (Matrix.single a b 1) = towerE T (ZMod 2) m hW a b := by
  change towerAddHom hW (Matrix.single a b 1) = _
  rw [towerAddHom_single, show (1 : ZMod 2).val = 1 from rfl, one_nsmul]

/-- The local identity of the tower copy is the tower unit `∑_a ε_{aa}`. -/
theorem towerHom_one (hlev : LevelsDisjoint T m U) (hWU : W ⊆ U) (hW : IsClopen W) :
    towerHom hlev hWU hW 1 = levelSum (T := T) (k := ZMod 2) m hW := by
  rw [towerHom_apply, levelSum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_eq_single a fun b hb => by rw [Matrix.one_apply_ne hb.symm, ZMod.val_zero,
      zero_nsmul], Matrix.one_apply_eq, show (1 : ZMod 2).val = 1 from rfl, one_nsmul]

/-- **Reading off a coefficient**: `ε_{aa} ψ(M) ε_{bb} = M_{ab} ε_{ab}`. -/
theorem towerE_mul_towerHom_mul_towerE (hlev : LevelsDisjoint T m U) (hWU : W ⊆ U)
    (hW : IsClopen W) (M : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) (ZMod 2))
    (a b : Fin (2 * m + 1)) :
    towerE T (ZMod 2) m hW a a * towerHom hlev hWU hW M * towerE T (ZMod 2) m hW b b =
      (M a b).val • towerE T (ZMod 2) m hW a b := by
  have hWW : W ∩ W ⊆ U := Set.inter_subset_left.trans hWU
  have hterm : ∀ a' b' : Fin (2 * m + 1),
      towerE T (ZMod 2) m hW a a * ((M a' b').val • towerE T (ZMod 2) m hW a' b') *
          towerE T (ZMod 2) m hW b b =
        if a' = a ∧ b' = b then (M a b).val • towerE T (ZMod 2) m hW a b else 0 := by
    intro a' b'
    rw [mul_smul_comm, smul_mul_assoc, towerE_mul_towerE hlev hWU hWU hW hW]
    by_cases ha : a = a'
    · subst ha
      rw [if_pos rfl, towerE_mul_towerE hlev hWW hWU (hW.inter hW) hW]
      by_cases hb : b' = b
      · subst hb
        rw [if_pos rfl, if_pos ⟨rfl, rfl⟩]
        congr 1
        unfold towerE
        congr 2
        exact charFn_congr _ _ (by rw [Set.inter_self, Set.inter_self])
      · rw [if_neg hb, smul_zero, if_neg fun h => hb h.2]
    · rw [if_neg ha, zero_mul, smul_zero, if_neg fun h => ha h.1.symm]
  simp only [towerHom_apply, Finset.mul_sum, Finset.sum_mul, hterm]
  rw [Fintype.sum_eq_single a fun a' ha' => Finset.sum_eq_zero fun b' _ => if_neg fun h => ha' h.1,
    Fintype.sum_eq_single b fun b' hb' => if_neg fun h => hb' h.2, if_pos ⟨rfl, rfl⟩]

/-- **The tower copy is injective** for nonempty `W`. -/
theorem towerHom_injective (hlev : LevelsDisjoint T m U) (hWU : W ⊆ U) (hW : IsClopen W)
    (hne : W.Nonempty) : Function.Injective (towerHom hlev hWU hW) := by
  intro M N h
  ext a b
  have h1 := towerE_mul_towerHom_mul_towerE hlev hWU hW M a b
  have h2 := towerE_mul_towerHom_mul_towerE hlev hWU hW N a b
  rw [h, h2] at h1
  have hne0 := towerE_ne_zero (k := ZMod 2) (T := T) hW hne a b
  have hval1 : (1 : ZMod 2).val = 1 := rfl
  have hv : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hv (M a b) with hM | hM <;> rcases hv (N a b) with hN | hN <;>
    simp only [hM, hN, ZMod.val_zero, hval1, zero_nsmul, one_nsmul] at h1 ⊢ <;>
    first | exact absurd h1 hne0 | exact absurd h1.symm hne0

#audit_axioms GroupApproximation.SimpleKazhdanSofic.towerHom_single
#audit_axioms GroupApproximation.SimpleKazhdanSofic.towerHom_one
#audit_axioms GroupApproximation.SimpleKazhdanSofic.towerE_mul_towerHom_mul_towerE
#audit_axioms GroupApproximation.SimpleKazhdanSofic.towerHom_injective

end SimpleKazhdanSofic
end GroupApproximation
