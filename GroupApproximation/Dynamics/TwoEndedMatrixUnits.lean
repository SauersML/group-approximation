import GroupApproximation.Dynamics.TwoEndedRepresentation
import GroupApproximation.Meta.AxiomGuard

/-!
# Matrix units of the two-ended crossed product: finitary blocks and shifts are units

`non_mf_groups_exist.tex`, the remark after `cor:dynamic-rank-budget` (tex 1774–1785 at origin/main
68481e4d7):

> Nevertheless its unit group is
> \[
>  R_X^\times\cong\GL_{\mathrm{fin}}(\mathbb Z,\F_2)\rtimes\mathbb Z,
> \]
> [...] removing that common shift leaves a finite invertible block extended by identity.

The isomorphism needs every element `g σ^a` of the right-hand side to be the action of a unit of
`R_X`.  For every commutative ring `k`, with the faithful action `rho k` of
`GroupApproximation.Dynamics.TwoEndedRepresentation`:

* `ptIndicator k r = 1_{\{r\}}` (the integer points are clopen: `isClopen_singleton_pt`);
* `matrixUnit k r c a = (a · 1_{\{r\}}) u^{r−c}` acts as the matrix unit `a E_{rc}`:
  `rho_matrixUnit_single`;
* `rho_sum_matrixUnit_eq`, `exists_rho_eq_of_hasFiniteMatrixSupport`: every operator of finite
  matrix support is `ρ(x)` for a finite sum `x` of matrix units;
* `exists_unit_rho_eq_of_mem_GLfin`: every `g ∈ GL_fin(ℤ, k)` is `ρ` of a unit, since the
  preimages of `g` and `g⁻¹` multiply to `1` by faithfulness;
* `exists_unit_rho_eq_mul_shiftGL_zpow` and the closed endpoint
  `printedTwoEndedFinitaryShiftUnits`: so is `g σ^a` for every `a ∈ ℤ`, using `ρ(u^a) = σ^a`.
-/

namespace GroupApproximation

namespace TwoEndedShift

open Finsupp

/-- The integer points of `ℤ ∪ {−∞, +∞}` are clopen. -/
theorem isClopen_singleton_pt (r : ℤ) : IsClopen ({pt r} : Set TwoEnded) :=
  ⟨isClosed_singleton, isOpen_singleton_pt r⟩

variable (k : Type*) [CommRing k]

/-- The point indicator `1_{\{r\}} ∈ LC(X, k)`. -/
noncomputable def ptIndicator (r : ℤ) : LocallyConstant TwoEnded k :=
  LocallyConstant.charFn k (isClopen_singleton_pt r)

theorem ptIndicator_pt (r j : ℤ) : ptIndicator k r (pt j) = if r = j then 1 else 0 := by
  rw [ptIndicator, LocallyConstant.coe_charFn]
  by_cases h : r = j
  · rw [if_pos h, h]
    exact Set.indicator_of_mem (Set.mem_singleton (pt j)) _
  · rw [if_neg h]
    exact Set.indicator_of_notMem
      (fun hm => h (pt_injective (Set.mem_singleton_iff.1 hm)).symm) _

theorem const_mul_ptIndicator_pt (r j : ℤ) (a : k) :
    (LocallyConstant.const TwoEnded a * ptIndicator k r) (pt j) = if r = j then a else 0 := by
  show a * ptIndicator k r (pt j) = if r = j then a else 0
  rw [ptIndicator_pt]
  split_ifs <;> simp

/-- **The matrix unit** `a E_{rc} = (a · 1_{\{r\}}) u^{r−c}` of `R_X`. -/
noncomputable def matrixUnit (r c : ℤ) (a : k) : ClopenCrossedProduct shift k :=
  ClopenCrossedProduct.coeff shift k (LocallyConstant.const TwoEnded a * ptIndicator k r) *
    ((ClopenCrossedProduct.unit shift k ^ (r - c) : (ClopenCrossedProduct shift k)ˣ) :
      ClopenCrossedProduct shift k)

/-- The matrix unit acts as `a E_{rc}`: `ρ(a E_{rc}) (b e_i) = δ_{ic} (a b) e_r`. -/
theorem rho_matrixUnit_single (r c i : ℤ) (a b : k) :
    rho k (matrixUnit k r c a) (single i b) = if i = c then single r (a * b) else 0 := by
  rw [matrixUnit, map_mul, rho_coeff, rho_unit_zpow, Module.End.mul_apply,
    FinitaryGL.shiftGL_zpow_single, diag_single, const_mul_ptIndicator_pt]
  by_cases h : i = c
  · subst h
    rw [if_pos (show r = i + (r - i) by ring), if_pos rfl, show i + (r - i) = r by ring]
  · rw [if_neg (show ¬ r = i + (r - c) by omega), if_neg h, zero_mul, Finsupp.single_zero]

/-- An operator supported in `S` is `ρ` of the finite sum `∑_{r,c ∈ S} A_{rc} E_{rc}`. -/
theorem rho_sum_matrixUnit_eq {S : Finset ℤ} {A : Module.End k (ℤ →₀ k)}
    (hA : FinitaryGL.SupportedIn k S A) :
    rho k (∑ r ∈ S, ∑ c ∈ S, matrixUnit k r c (A (single c 1) r)) = A := by
  refine Finsupp.lhom_ext fun i b => ?_
  have hev : ∀ (s : Finset ℤ) (F : ℤ → ℤ →₀ k) (l : ℤ), (∑ x ∈ s, F x) l = ∑ x ∈ s, F x l :=
    fun s F l => map_sum (Finsupp.applyAddHom l) F s
  have hsum : ∀ r, rho k (∑ c ∈ S, matrixUnit k r c (A (single c 1) r)) (single i b) =
      if i ∈ S then single r (A (single i 1) r * b) else 0 := fun r => by
    rw [map_sum, LinearMap.sum_apply]
    simp only [rho_matrixUnit_single]
    exact Finset.sum_ite_eq S i (fun c => single r (A (single c 1) r * b))
  have hAi : A (single i b) = b • A (single i 1) := by
    rw [← Finsupp.smul_single_one i b, map_smul]
  rw [map_sum, LinearMap.sum_apply]
  simp only [hsum]
  by_cases hi : i ∈ S
  · simp only [if_pos hi]
    ext l
    rw [hev]
    simp only [Finsupp.single_apply]
    rw [Finset.sum_ite_eq', hAi, Finsupp.smul_apply, smul_eq_mul]
    by_cases hl : l ∈ S
    · rw [if_pos hl, mul_comm]
    · rw [if_neg hl,
        (mem_supported' k _).1 (hA.1 (single i 1)) l (fun h => hl (Finset.mem_coe.1 h)), mul_zero]
  · simp only [if_neg hi, Finset.sum_const_zero]
    rw [hAi, hA.apply_single_eq_zero hi, smul_zero]

/-- Every operator of finite matrix support is the action of an element of `R_X`. -/
theorem exists_rho_eq_of_hasFiniteMatrixSupport {A : Module.End k (ℤ →₀ k)}
    (hA : FinitaryGL.HasFiniteMatrixSupport k A) : ∃ x, rho k x = A := by
  obtain ⟨S, hS⟩ := (FinitaryGL.hasFiniteMatrixSupport_iff A).1 hA
  exact ⟨_, rho_sum_matrixUnit_eq k hS⟩

theorem exists_rho_eq_of_mem_GLfin {g : LinearMap.GeneralLinearGroup k (ℤ →₀ k)}
    (hg : g ∈ FinitaryGL.GLfin k) : ∃ x, rho k x = (g : Module.End k (ℤ →₀ k)) := by
  obtain ⟨y, hy⟩ :=
    exists_rho_eq_of_hasFiniteMatrixSupport k (A := (g : Module.End k (ℤ →₀ k)) - 1) hg
  exact ⟨1 + y, by rw [map_add, map_one, hy]; abel⟩

/-- **"a finite invertible block extended by identity"** (tex 1785) comes from a unit of `R_X`. -/
theorem exists_unit_rho_eq_of_mem_GLfin {g : LinearMap.GeneralLinearGroup k (ℤ →₀ k)}
    (hg : g ∈ FinitaryGL.GLfin k) :
    ∃ x : (ClopenCrossedProduct shift k)ˣ,
      rho k (x : ClopenCrossedProduct shift k) = (g : Module.End k (ℤ →₀ k)) := by
  obtain ⟨x, hx⟩ := exists_rho_eq_of_mem_GLfin k hg
  obtain ⟨x', hx'⟩ := exists_rho_eq_of_mem_GLfin k ((FinitaryGL.GLfin k).inv_mem hg)
  have h1 : x * x' = 1 := rho_injective k (by
    rw [map_mul, map_one, hx, hx', ← Units.val_mul, mul_inv_cancel, Units.val_one])
  have h2 : x' * x = 1 := rho_injective k (by
    rw [map_mul, map_one, hx, hx', ← Units.val_mul, inv_mul_cancel, Units.val_one])
  exact ⟨⟨x, x', h1, h2⟩, hx⟩

theorem exists_unit_rho_eq_mul_shiftGL_zpow {g : LinearMap.GeneralLinearGroup k (ℤ →₀ k)}
    (hg : g ∈ FinitaryGL.GLfin k) (a : ℤ) :
    ∃ x : (ClopenCrossedProduct shift k)ˣ, rho k (x : ClopenCrossedProduct shift k) =
      ((g * FinitaryGL.shiftGL k ^ a : LinearMap.GeneralLinearGroup k (ℤ →₀ k)) :
        Module.End k (ℤ →₀ k)) := by
  obtain ⟨x, hx⟩ := exists_unit_rho_eq_of_mem_GLfin k hg
  exact ⟨x * ClopenCrossedProduct.unit shift k ^ a, by
    rw [Units.val_mul x, map_mul, hx, rho_unit_zpow, Units.val_mul g]⟩

/-- The surjectivity half of `R_X^× ≅ GL_fin(ℤ, k) ⋊ ℤ` (tex 1774–1785), over every commutative
ring `k`: every `g σ^a` with `g ∈ GL_fin(ℤ, k)` and `a ∈ ℤ` is the action of a unit of `R_X`. -/
def PrintedTwoEndedFinitaryShiftUnits : Prop :=
  ∀ (k : Type) [CommRing k] (g : LinearMap.GeneralLinearGroup k (ℤ →₀ k)),
    g ∈ FinitaryGL.GLfin k → ∀ a : ℤ, ∃ x : (ClopenCrossedProduct shift k)ˣ,
      rho k (x : ClopenCrossedProduct shift k) =
        ((g * FinitaryGL.shiftGL k ^ a : LinearMap.GeneralLinearGroup k (ℤ →₀ k)) :
          Module.End k (ℤ →₀ k))

theorem printedTwoEndedFinitaryShiftUnits : PrintedTwoEndedFinitaryShiftUnits :=
  fun k _ _ hg a => exists_unit_rho_eq_mul_shiftGL_zpow k hg a

end TwoEndedShift

end GroupApproximation

open GroupApproximation

#audit_closed_axioms GroupApproximation.TwoEndedShift.printedTwoEndedFinitaryShiftUnits
#audit_axioms GroupApproximation.TwoEndedShift.rho_matrixUnit_single
#audit_axioms GroupApproximation.TwoEndedShift.rho_sum_matrixUnit_eq
#audit_axioms GroupApproximation.TwoEndedShift.exists_unit_rho_eq_of_mem_GLfin
