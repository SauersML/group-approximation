import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralSimplicityStatement
import GroupApproximation.Manuscript.SimpleKazhdanSofic.TowerMatrixUnits
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.Group

/-!
# The matrix units `ε_ab` for a group action

`simple_kazhdan_sofic_group.tex` at 37551fd93, subsection "Simplicity" (l.176–182):

> For $a,b\in B_w$ put $\epsilon_{ab}=e_{aV}u_{ab^{-1}}$. Since
> $\epsilon_{ab}\epsilon_{a'b'}=e_{a(V\cap b^{-1}a'V)}\,u_{ab^{-1}a'b'^{-1}}$ and $b^{-1}a'\in B_{2w}$, we
> get $\epsilon_{ab}\epsilon_{a'b'}=\delta_{ba'}\epsilon_{ab'}$. As $h\ne I_3$, $V$ is nonempty, so the
> $\epsilon_{ab}$ span a ring $A_V\cong M_{|B_w|}(\F_2)$ with unit $e=\sum_a\epsilon_{aa}$.

Over a covariant pair `(coeff, u)` (`GeneralSimplicityStatement`) and a finite `B ⊆ Λ` whose
translates of `V` are pairwise disjoint:

* `epsilon_mul_epsilon`: `ε_ab ε_a'b' = δ_{ba'} ε_ab'`;
* `epsilon_ne_zero`: `ε_ab ≠ 0` for nonempty `V`;
* `epsilonHom hcov hdisj hV : M_B(F_2) →ₙ+* R`, `M ↦ ∑_{a,b} M_ab ε_ab`, with `epsilonHom_single`
  (`E_ab ↦ ε_ab`) and `epsilonHom_injective`. Its range is `A_V`, and its local identity is `e`.

The coefficient `M_ab ∈ F_2` acts through `ZMod.val`, and `R` has characteristic `2` because it contains
`coeff (LC(Z, F_2))`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace General

open Pointwise

variable {Λ Z R : Type*} [Group Λ] [TopologicalSpace Z] [MulAction Λ Z] [ContinuousConstSMul Λ Z]
  [Ring R] {coeff : LocallyConstant Z (ZMod 2) →+* R} {u : Λ →* Rˣ}

section CharTwo

variable (coeff)
include coeff

theorem one_add_one_eq_zero : (1 : R) + 1 = 0 := by
  have h : (1 : LocallyConstant Z (ZMod 2)) + 1 = 0 := by
    ext x
    simp only [LocallyConstant.add_apply, LocallyConstant.one_apply, LocallyConstant.zero_apply]
    decide
  rw [← map_one coeff, ← map_add, h, map_zero]

theorem two_nsmul_eq_zero (y : R) : 2 • y = 0 := by
  rw [two_nsmul, ← one_mul y, ← add_mul, one_add_one_eq_zero coeff, zero_mul]

theorem mod_two_nsmul (n : ℕ) (y : R) : (n % 2) • y = n • y := by
  conv_rhs => rw [← Nat.mod_add_div n 2]
  rw [add_nsmul, mul_nsmul, two_nsmul_eq_zero coeff, nsmul_zero, add_zero]

theorem val_add_nsmul (x x' : ZMod 2) (y : R) : (x + x').val • y = x.val • y + x'.val • y := by
  rw [ZMod.val_add, mod_two_nsmul coeff, add_nsmul]

theorem val_mul_nsmul (x x' : ZMod 2) (y : R) : (x * x').val • y = x.val • x'.val • y := by
  rw [ZMod.val_mul, mod_two_nsmul coeff, mul_nsmul']

end CharTwo

theorem nsmul_mul_nsmul (n n' : ℕ) (y y' : R) : (n • y) * (n' • y') = (n * n') • (y * y') := by
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]

variable (hcov : IsCovariantPair coeff u)
include hcov

/-- **The printed product rule**: `ε_ab ε_a'b' = δ_{ba'} ε_ab'`. -/
theorem epsilon_mul_epsilon [DecidableEq Λ] {B : Finset Λ} {V : Set Z} (hV : IsClopen V)
    (hdisj : TranslatesDisjoint B V) {a b a' b' : Λ} (hb : b ∈ B) (ha' : a' ∈ B) :
    epsilon coeff u hV a b * epsilon coeff u hV a' b' =
      if b = a' then epsilon coeff u hV a b' else 0 := by
  unfold epsilon
  rw [mul_assoc, ← mul_assoc (u (a * b⁻¹) : R), hcov.covariance (a * b⁻¹) (isClopen_smul a' hV),
    mul_assoc, ← Units.val_mul, ← map_mul u, ← mul_assoc, ← map_mul coeff]
  split_ifs with hba
  · subst hba
    have hset : a • V ∩ (a * b⁻¹) • b • V = a • V := by
      rw [smul_smul, inv_mul_cancel_right, Set.inter_self]
    have hexp : a * b⁻¹ * (b * b'⁻¹) = a * b'⁻¹ := by group
    rw [charFn_mul_charFn_inter, hexp]
    congr 2
    exact charFn_congr _ _ hset
  · have h1 : Disjoint ((a * b⁻¹) • (b • V)) ((a * b⁻¹) • (a' • V)) :=
      (Set.disjoint_image_iff (MulAction.injective (a * b⁻¹))).2 (hdisj b hb a' ha' hba)
    rw [smul_smul, inv_mul_cancel_right] at h1
    rw [ClopenCrossedProduct.charFn_mul_charFn_of_disjoint (ZMod 2) _ _ h1, map_zero, zero_mul]

/-- **`ε_ab ≠ 0`** for nonempty `V`. -/
theorem epsilon_ne_zero {V : Set Z} (hV : IsClopen V) (hne : V.Nonempty) (a b : Λ) :
    epsilon coeff u hV a b ≠ 0 := by
  intro h
  have h2 : coeff (LocallyConstant.charFn (ZMod 2) (isClopen_smul a hV)) = coeff 0 := by
    have h3 := congrArg (· * (((u (a * b⁻¹))⁻¹ : Rˣ) : R)) h
    simpa only [epsilon, mul_assoc, Units.mul_inv, mul_one, zero_mul, map_zero] using h3
  have h4 := LocallyConstant.congr_fun (hcov.injective h2) (a • hne.some)
  rw [LocallyConstant.zero_apply, LocallyConstant.charFn_eq_zero] at h4
  exact h4 (Set.smul_mem_smul_set hne.some_mem)

variable {B : Finset Λ} {V : Set Z}

omit hcov in
variable (coeff u) in
/-- The additive map `M ↦ ∑_{a,b} M_ab ε_ab`. -/
noncomputable def epsilonAddHom (B : Finset Λ) (hV : IsClopen V) : Matrix B B (ZMod 2) →+ R where
  toFun M := ∑ a : B, ∑ b : B, (M a b).val • epsilon coeff u hV a b
  map_zero' := by simp only [Matrix.zero_apply, ZMod.val_zero, zero_nsmul, Finset.sum_const_zero]
  map_add' M N := by simp only [Matrix.add_apply, val_add_nsmul coeff, Finset.sum_add_distrib]

omit hcov in
theorem epsilonAddHom_apply (hV : IsClopen V) (M : Matrix B B (ZMod 2)) :
    epsilonAddHom coeff u B hV M = ∑ a : B, ∑ b : B, (M a b).val • epsilon coeff u hV a b := rfl

variable [DecidableEq Λ]

omit hcov in
theorem epsilonAddHom_single (hV : IsClopen V) (a b : B) (x : ZMod 2) :
    epsilonAddHom coeff u B hV (Matrix.single a b x) = x.val • epsilon coeff u hV a b := by
  have h1 : ∀ a' : B, a' ≠ a →
      ∑ b', (Matrix.single a b x a' b').val • epsilon coeff u hV a' b' = 0 := by
    intro a' ha'
    refine Finset.sum_eq_zero fun b' _ => ?_
    rw [Matrix.single_apply_of_row_ne ha'.symm, ZMod.val_zero, zero_nsmul]
  have h2 : ∀ b' : B, b' ≠ b → (Matrix.single a b x a b').val • epsilon coeff u hV a b' = 0 := by
    intro b' hb'
    rw [Matrix.single_apply_of_col_ne a a hb'.symm x, ZMod.val_zero, zero_nsmul]
  rw [epsilonAddHom_apply, Fintype.sum_eq_single a h1, Fintype.sum_eq_single b h2,
    Matrix.single_apply_same]

theorem epsilonAddHom_single_mul_single (hdisj : TranslatesDisjoint B V) (hV : IsClopen V)
    (a b c d : B) (x y : ZMod 2) :
    epsilonAddHom coeff u B hV (Matrix.single a b x * Matrix.single c d y) =
      epsilonAddHom coeff u B hV (Matrix.single a b x) *
        epsilonAddHom coeff u B hV (Matrix.single c d y) := by
  rw [epsilonAddHom_single, epsilonAddHom_single, nsmul_mul_nsmul,
    epsilon_mul_epsilon hcov hV hdisj b.2 c.2]
  by_cases hbc : b = c
  · subst hbc
    rw [Matrix.single_mul_single_same, epsilonAddHom_single, if_pos rfl, val_mul_nsmul coeff,
      smul_smul]
  · rw [Matrix.single_mul_single_of_ne (h := hbc), map_zero,
      if_neg fun h => hbc (Subtype.ext h), smul_zero]

/-- `ψ` is multiplicative: both sides are biadditive and agree on matrix units. -/
theorem epsilonAddHom_mul (hdisj : TranslatesDisjoint B V) (hV : IsClopen V)
    (M N : Matrix B B (ZMod 2)) :
    epsilonAddHom coeff u B hV (M * N) = epsilonAddHom coeff u B hV M * epsilonAddHom coeff u B hV N := by
  induction M using Matrix.induction_on' with
  | h_zero => rw [zero_mul, map_zero, zero_mul]
  | h_add p q hp hq => rw [add_mul, map_add, map_add, add_mul, hp, hq]
  | h_std_basis a b x =>
    induction N using Matrix.induction_on' with
    | h_zero => rw [mul_zero, map_zero, mul_zero]
    | h_add p q hp hq => rw [mul_add, map_add, map_add, mul_add, hp, hq]
    | h_std_basis c d y => exact epsilonAddHom_single_mul_single hcov hdisj hV a b c d x y

/-- **The copy `ψ : M_B(F_2) →ₙ+* R`** of the printed `A_V ≅ M_{|B_w|}(F_2)`. -/
noncomputable def epsilonHom (hdisj : TranslatesDisjoint B V) (hV : IsClopen V) :
    Matrix B B (ZMod 2) →ₙ+* R where
  toFun := epsilonAddHom coeff u B hV
  map_zero' := map_zero _
  map_add' := map_add _
  map_mul' := epsilonAddHom_mul hcov hdisj hV

theorem epsilonHom_apply (hdisj : TranslatesDisjoint B V) (hV : IsClopen V) (M : Matrix B B (ZMod 2)) :
    epsilonHom hcov hdisj hV M = ∑ a : B, ∑ b : B, (M a b).val • epsilon coeff u hV a b := rfl

/-- `ψ(E_ab) = ε_ab`. -/
theorem epsilonHom_single (hdisj : TranslatesDisjoint B V) (hV : IsClopen V) (a b : B) :
    epsilonHom hcov hdisj hV (Matrix.single a b 1) = epsilon coeff u hV a b := by
  change epsilonAddHom coeff u B hV (Matrix.single a b 1) = _
  rw [epsilonAddHom_single, show (1 : ZMod 2).val = 1 from rfl, one_nsmul]

/-- **Reading off a coefficient**: `ε_aa ψ(M) ε_bb = M_ab ε_ab`. -/
theorem epsilon_mul_epsilonHom_mul_epsilon (hdisj : TranslatesDisjoint B V) (hV : IsClopen V)
    (M : Matrix B B (ZMod 2)) (a b : B) :
    epsilon coeff u hV a a * epsilonHom hcov hdisj hV M * epsilon coeff u hV b b =
      (M a b).val • epsilon coeff u hV a b := by
  have hterm : ∀ a' b' : B,
      epsilon coeff u hV a a * ((M a' b').val • epsilon coeff u hV a' b') * epsilon coeff u hV b b =
        if a' = a ∧ b' = b then (M a b).val • epsilon coeff u hV a b else 0 := by
    intro a' b'
    rw [mul_smul_comm, smul_mul_assoc, epsilon_mul_epsilon hcov hV hdisj a.2 a'.2]
    by_cases ha : a = a'
    · subst ha
      rw [if_pos rfl, epsilon_mul_epsilon hcov hV hdisj b'.2 b.2]
      by_cases hb : b' = b
      · subst hb
        rw [if_pos rfl, if_pos ⟨rfl, rfl⟩]
      · rw [if_neg fun h => hb (Subtype.ext h), smul_zero, if_neg fun h => hb h.2]
    · rw [if_neg fun h => ha (Subtype.ext h), zero_mul, smul_zero, if_neg fun h => ha h.1.symm]
  simp only [epsilonHom_apply, Finset.mul_sum, Finset.sum_mul, hterm]
  rw [Fintype.sum_eq_single a fun a' ha' => Finset.sum_eq_zero fun b' _ => if_neg fun h => ha' h.1,
    Fintype.sum_eq_single b fun b' hb' => if_neg fun h => hb' h.2, if_pos ⟨rfl, rfl⟩]

/-- **`ψ` is injective** for nonempty `V`. -/
theorem epsilonHom_injective (hdisj : TranslatesDisjoint B V) (hV : IsClopen V) (hne : V.Nonempty) :
    Function.Injective (epsilonHom hcov hdisj hV) := by
  intro M N h
  ext a b
  have h1 := epsilon_mul_epsilonHom_mul_epsilon hcov hdisj hV M a b
  have h2 := epsilon_mul_epsilonHom_mul_epsilon hcov hdisj hV N a b
  rw [h, h2] at h1
  have hne0 := epsilon_ne_zero hcov hV hne (a : Λ) b
  have hval1 : (1 : ZMod 2).val = 1 := rfl
  have hv : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hv (M a b) with hM | hM <;> rcases hv (N a b) with hN | hN <;>
    simp only [hM, hN, ZMod.val_zero, hval1, zero_nsmul, one_nsmul] at h1 ⊢ <;>
    first | exact absurd h1 hne0 | exact absurd h1.symm hne0

#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.epsilon_mul_epsilon
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.epsilon_ne_zero
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.epsilonHom_single
#audit_axioms GroupApproximation.SimpleKazhdanSofic.General.epsilonHom_injective

end General
end SimpleKazhdanSofic
end GroupApproximation
