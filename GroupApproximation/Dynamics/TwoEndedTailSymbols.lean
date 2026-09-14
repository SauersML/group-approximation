import GroupApproximation.Dynamics.TwoEndedRepresentation
import GroupApproximation.Algebra.LaurentMonomialUnits
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.Linarith

/-!
# Laurent symbols at the two ends and translation of the far tails

`non_mf_groups_exist.tex`, the remark after `cor:dynamic-rank-budget` (tex 1780–1782):

> A unit has Laurent symbols $z^{a_-},z^{a_+}$ at the two ends and acts by these translations on
> the two sufficiently distant tails.

Both endpoints `±∞` of `X = ℤ ∪ {−∞, +∞}` are fixed by `T`.  Freezing the coefficients of
`x = Σ_j x_j u^j` at an endpoint `e` gives the Laurent symbol `Σ_j x_j(e) z^j ∈ k[z, z⁻¹]`.  It is
realized here through the operator `symbolOp e x` on `k^{(ℤ)}`, in which a coefficient acts by the
scalar `x_j(e)` and `u` by the bilateral shift; `symbol e x` is its column at `e_0`.  The symbol is
multiplicative (`symbol_mul`), so a unit has a unit symbol, which over `𝔽₂` is a monomial `z^a`
(`LaurentMonomialUnits`).  A coefficient is locally constant, hence constant near each endpoint, so
far out on either tail the faithful action `ρ` agrees with `symbolOp` (`exists_tail_pos`,
`exists_tail_neg`), and `ρ(u)` translates the far tail by `a`.

* `symbolOp k e he`, `symbolOp_apply_single_apply`, `symbol k e he x`, `symbol_mul`, `symbol_one`;
* `exists_tail_pos`, `exists_tail_neg`;
* `exists_tail_translation_pos`, `exists_tail_translation_neg`: over `𝔽₂` a unit translates each far
  tail, `ρ(u) e_i = e_{i + a_±}`.
-/

namespace GroupApproximation

namespace TwoEndedShift

open Finsupp Filter Topology
open Multiplicative (ofAdd toAdd)

theorem shift_zpow_apply_of_fixed {e : TwoEnded} (he : shift e = e) (n : ℤ) :
    (shift ^ n) e = e := by
  have hsymm : shift.symm e = e := by
    calc shift.symm e = shift.symm (shift e) := by rw [he]
      _ = e := shift.symm_apply_apply e
  induction n using Int.induction_on with
  | zero => rw [zpow_zero, Homeomorph.one_apply]
  | succ n ih => rw [zpow_add_one, Homeomorph.mul_apply, he, ih]
  | pred n ih => rw [zpow_sub_one, Homeomorph.mul_apply, Homeomorph.inv_apply, hsymm, ih]

variable (k : Type*) [CommRing k]

/-- Evaluation of a coefficient of `R_X` at a point `e` of `X`. -/
noncomputable def evalCoeff (e : TwoEnded) : ClopenCoeff shift k →+* k where
  toFun a := (ClopenCoeff.of shift k).symm a e
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem evalCoeff_apply (e : TwoEnded) (a : ClopenCoeff shift k) :
    evalCoeff k e a = (ClopenCoeff.of shift k).symm a e :=
  rfl

/-- The coefficients of `R_X` acting on `k^{(ℤ)}` by the scalars `a(e)`. -/
noncomputable def scalarHom (e : TwoEnded) : ClopenCoeff shift k →+* Module.End k (ℤ →₀ k) :=
  (algebraMap k (Module.End k (ℤ →₀ k))).comp (evalCoeff k e)

theorem scalarHom_apply (e : TwoEnded) (a : ClopenCoeff shift k) (w : ℤ →₀ k) :
    scalarHom k e a w = evalCoeff k e a • w := by
  rw [scalarHom, RingHom.comp_apply, Module.algebraMap_end_apply]

/-- **The symbol operator at a fixed point** `e` of `T`: a coefficient acts by its value at `e` and
`u` by the bilateral shift. -/
noncomputable def symbolOp (e : TwoEnded) (he : shift e = e) :
    ClopenCrossedProduct shift k →+* Module.End k (ℤ →₀ k) :=
  SkewMonoidAlgebra.liftNCRingHom (scalarHom k e) (shiftHom k) fun {x y} => by
    have hx : evalCoeff k e (y • x) = evalCoeff k e x := by
      show (ClopenCoeff.of shift k).symm x ((shift ^ (-toAdd y)) e) =
        (ClopenCoeff.of shift k).symm x e
      rw [shift_zpow_apply_of_fixed he]
    rw [scalarHom, RingHom.comp_apply, RingHom.comp_apply, hx]
    exact Algebra.commutes _ _

theorem symbolOp_single (e : TwoEnded) (he : shift e = e) (g : Multiplicative ℤ)
    (a : ClopenCoeff shift k) :
    symbolOp k e he (SkewMonoidAlgebra.single g a) = scalarHom k e a * shiftHom k g := by
  show SkewMonoidAlgebra.liftNC (scalarHom k e : ClopenCoeff shift k →+ Module.End k (ℤ →₀ k))
    (shiftHom k) (SkewMonoidAlgebra.single g a) = scalarHom k e a * shiftHom k g
  exact SkewMonoidAlgebra.liftNC_single _ _ _ _

/-- `(symbolOp e x (c e_i))_l = x_{l−i}(e) · c`. -/
theorem symbolOp_apply_single_apply (e : TwoEnded) (he : shift e = e)
    (x : ClopenCrossedProduct shift k) (i l : ℤ) (c : k) :
    symbolOp k e he x (single i c) l =
      (ClopenCoeff.of shift k).symm (SkewMonoidAlgebra.coeff x (ofAdd (l - i))) e * c := by
  induction x using SkewMonoidAlgebra.induction_on with
  | zero => simp
  | single g a =>
      rw [symbolOp_single, Module.End.mul_apply, shiftHom_apply, FinitaryGL.shiftGL_zpow_single,
        scalarHom_apply, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply,
        SkewMonoidAlgebra.coeff_single_apply, evalCoeff_apply]
      by_cases h : g = ofAdd (l - i)
      · have h' : i + toAdd g = l := by
          rw [h, toAdd_ofAdd]
          omega
        rw [if_pos h', if_pos h]
      · have h' : ¬ i + toAdd g = l := fun h'' => by
          have ht : toAdd g = l - i := by omega
          exact h (by rw [← ht, ofAdd_toAdd])
        rw [if_neg h', if_neg h]
        simp
  | add x y hx hy =>
      rw [map_add, LinearMap.add_apply, Finsupp.add_apply, hx, hy, SkewMonoidAlgebra.coeff_add,
        Finsupp.add_apply, map_add]
      exact (add_mul _ _ _).symm

theorem symbolOp_apply_single_one (e : TwoEnded) (he : shift e = e)
    (x : ClopenCrossedProduct shift k) (i l : ℤ) :
    symbolOp k e he x (single i 1) l = symbolOp k e he x (single 0 1) (l - i) := by
  rw [symbolOp_apply_single_apply, symbolOp_apply_single_apply, sub_zero]

/-- **The Laurent symbol** `Σ_j x_j(e) z^j` of `x` at a fixed point `e`. -/
noncomputable def symbol (e : TwoEnded) (he : shift e = e) (x : ClopenCrossedProduct shift k) :
    AddMonoidAlgebra k ℤ :=
  AddMonoidAlgebra.ofCoeff (symbolOp k e he x (single 0 1))

theorem symbol_coeff (e : TwoEnded) (he : shift e = e) (x : ClopenCrossedProduct shift k) (j : ℤ) :
    (symbol k e he x).coeff j = symbolOp k e he x (single 0 1) j :=
  rfl

theorem symbolOp_apply_eq_sum (e : TwoEnded) (he : shift e = e) (x : ClopenCrossedProduct shift k)
    (v : ℤ →₀ k) (m : ℤ) :
    symbolOp k e he x v m = v.sum fun j r => r * symbolOp k e he x (single 0 1) (m - j) := by
  conv_lhs => rw [← Finsupp.sum_single v]
  rw [map_finsuppSum, Finsupp.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  show symbolOp k e he x (single j (v j)) m = v j * symbolOp k e he x (single 0 1) (m - j)
  rw [← Finsupp.smul_single_one j (v j), map_smul, Finsupp.smul_apply, smul_eq_mul,
    symbolOp_apply_single_one]

/-- **The symbol is multiplicative**: `symbol(x y) = symbol(y) symbol(x)` in `k[z, z⁻¹]`. -/
theorem symbol_mul (e : TwoEnded) (he : shift e = e) (x y : ClopenCrossedProduct shift k) :
    symbol k e he (x * y) = symbol k e he y * symbol k e he x := by
  classical
  have hinner : ∀ (m j : ℤ) (r : k),
      ((symbol k e he x).coeff.sum fun l s => if j + l = m then r * s else 0) =
        r * (symbol k e he x).coeff (m - j) := by
    intro m j r
    simp only [Finsupp.sum]
    rw [Finset.sum_eq_single (m - j)]
    · rw [if_pos (by omega)]
    · intro l _ hl
      rw [if_neg (by omega)]
    · intro hmj
      rw [if_pos (by omega), Finsupp.notMem_support_iff.1 hmj, mul_zero]
  refine AddMonoidAlgebra.coeff_injective (Finsupp.ext fun m => ?_)
  rw [AddMonoidAlgebra.coeff_mul, symbol_coeff, map_mul, Module.End.mul_apply,
    symbolOp_apply_eq_sum]
  simp only [hinner]
  rfl

theorem symbol_one (e : TwoEnded) (he : shift e = e) :
    symbol k e he (1 : ClopenCrossedProduct shift k) = 1 := by
  refine AddMonoidAlgebra.coeff_injective (Finsupp.ext fun m => ?_)
  rw [symbol_coeff, map_one, Module.End.one_apply, AddMonoidAlgebra.one_def,
    AddMonoidAlgebra.coeff_single]

omit [CommRing k] in
theorem eventually_pt_atTop_eq (f : LocallyConstant TwoEnded k) :
    ∀ᶠ l in atTop, f (pt l) = f posInf := by
  have hU : IsOpen {y : TwoEnded | f y = f posInf} := f.isLocallyConstant.isOpen_fiber (f posInf)
  exact tendsto_pt_atTop (hU.mem_nhds rfl)

omit [CommRing k] in
theorem eventually_pt_atBot_eq (f : LocallyConstant TwoEnded k) :
    ∀ᶠ l in atBot, f (pt l) = f negInf := by
  have hU : IsOpen {y : TwoEnded | f y = f negInf} := f.isLocallyConstant.isOpen_fiber (f negInf)
  exact tendsto_pt_atBot (hU.mem_nhds rfl)

/-- **The far positive tail** (tex 1781–1782): for all large `i`, `ρ(x)` agrees with the symbol
operator at `+∞` on `c e_i`. -/
theorem exists_tail_pos (x : ClopenCrossedProduct shift k) :
    ∃ N : ℤ, ∀ i, N ≤ i → ∀ c : k,
      rho k x (single i c) = symbolOp k posInf shift_posInf x (single i c) := by
  classical
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1
    ((Filter.eventually_all_finset (SkewMonoidAlgebra.support x)).2 fun g _ =>
      eventually_pt_atTop_eq k ((ClopenCoeff.of shift k).symm (SkewMonoidAlgebra.coeff x g)))
  refine ⟨N₀ + ∑ g ∈ SkewMonoidAlgebra.support x, |toAdd g|, fun i hi c =>
    Finsupp.ext fun l => ?_⟩
  rw [rho_apply_single_apply, symbolOp_apply_single_apply]
  by_cases hg : ofAdd (l - i) ∈ SkewMonoidAlgebra.support x
  · have hB : |toAdd (ofAdd (l - i))| ≤ ∑ g ∈ SkewMonoidAlgebra.support x, |toAdd g| :=
      Finset.single_le_sum (fun g _ => abs_nonneg (toAdd g)) hg
    rw [toAdd_ofAdd] at hB
    have h1 := neg_abs_le (l - i)
    have hl : N₀ ≤ l := by linarith
    rw [hN₀ l hl _ hg]
  · rw [SkewMonoidAlgebra.notMem_support_iff.1 hg, map_zero]
    rfl

/-- **The far negative tail**: for all small `i`, `ρ(x)` agrees with the symbol operator at `−∞` on
`c e_i`. -/
theorem exists_tail_neg (x : ClopenCrossedProduct shift k) :
    ∃ N : ℤ, ∀ i, i ≤ N → ∀ c : k,
      rho k x (single i c) = symbolOp k negInf shift_negInf x (single i c) := by
  classical
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atBot.1
    ((Filter.eventually_all_finset (SkewMonoidAlgebra.support x)).2 fun g _ =>
      eventually_pt_atBot_eq k ((ClopenCoeff.of shift k).symm (SkewMonoidAlgebra.coeff x g)))
  refine ⟨N₀ - ∑ g ∈ SkewMonoidAlgebra.support x, |toAdd g|, fun i hi c =>
    Finsupp.ext fun l => ?_⟩
  rw [rho_apply_single_apply, symbolOp_apply_single_apply]
  by_cases hg : ofAdd (l - i) ∈ SkewMonoidAlgebra.support x
  · have hB : |toAdd (ofAdd (l - i))| ≤ ∑ g ∈ SkewMonoidAlgebra.support x, |toAdd g| :=
      Finset.single_le_sum (fun g _ => abs_nonneg (toAdd g)) hg
    rw [toAdd_ofAdd] at hB
    have h1 := le_abs_self (l - i)
    have hl : l ≤ N₀ := by linarith
    rw [hN₀ l hl _ hg]
  · rw [SkewMonoidAlgebra.notMem_support_iff.1 hg, map_zero]
    rfl

theorem symbol_units_mul_inv (e : TwoEnded) (he : shift e = e)
    (u : (ClopenCrossedProduct shift k)ˣ) :
    symbol k e he (u : ClopenCrossedProduct shift k) *
      symbol k e he ((u⁻¹ : (ClopenCrossedProduct shift k)ˣ) : ClopenCrossedProduct shift k) =
      1 := by
  rw [← symbol_mul, Units.inv_mul, symbol_one]

theorem symbolOp_translation (e : TwoEnded) (he : shift e = e)
    (u : (ClopenCrossedProduct shift (ZMod 2))ˣ) {a : ℤ}
    (ha : (symbol (ZMod 2) e he (u : ClopenCrossedProduct shift (ZMod 2))).coeff =
      Finsupp.single a 1) (i : ℤ) :
    symbolOp (ZMod 2) e he (u : ClopenCrossedProduct shift (ZMod 2)) (single i 1) =
      single (i + a) 1 := by
  refine Finsupp.ext fun l => ?_
  rw [symbolOp_apply_single_one, ← symbol_coeff, ha, Finsupp.single_apply, Finsupp.single_apply]
  by_cases h : i + a = l
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

/-- **A unit translates the far positive tail** (tex 1780–1782): over `𝔽₂` its symbol at `+∞` is
`z^{a₊}`, and `ρ(u) e_i = e_{i + a₊}` for all large `i`. -/
theorem exists_tail_translation_pos (u : (ClopenCrossedProduct shift (ZMod 2))ˣ) :
    ∃ a N : ℤ, ∀ i, N ≤ i →
      rho (ZMod 2) (u : ClopenCrossedProduct shift (ZMod 2)) (single i 1) = single (i + a) 1 := by
  obtain ⟨a, ha⟩ := LaurentMonomialUnits.exists_single_one_of_mul_eq_one_zmodTwo
    (symbol_units_mul_inv (ZMod 2) posInf shift_posInf u)
  obtain ⟨N, hN⟩ := exists_tail_pos (ZMod 2) (u : ClopenCrossedProduct shift (ZMod 2))
  exact ⟨a, N, fun i hi => (hN i hi 1).trans (symbolOp_translation posInf shift_posInf u ha i)⟩

/-- **A unit translates the far negative tail**: over `𝔽₂` its symbol at `−∞` is `z^{a₋}`, and
`ρ(u) e_i = e_{i + a₋}` for all small `i`. -/
theorem exists_tail_translation_neg (u : (ClopenCrossedProduct shift (ZMod 2))ˣ) :
    ∃ a N : ℤ, ∀ i, i ≤ N →
      rho (ZMod 2) (u : ClopenCrossedProduct shift (ZMod 2)) (single i 1) = single (i + a) 1 := by
  obtain ⟨a, ha⟩ := LaurentMonomialUnits.exists_single_one_of_mul_eq_one_zmodTwo
    (symbol_units_mul_inv (ZMod 2) negInf shift_negInf u)
  obtain ⟨N, hN⟩ := exists_tail_neg (ZMod 2) (u : ClopenCrossedProduct shift (ZMod 2))
  exact ⟨a, N, fun i hi => (hN i hi 1).trans (symbolOp_translation negInf shift_negInf u ha i)⟩

end TwoEndedShift

end GroupApproximation

open GroupApproximation

#audit_axioms GroupApproximation.TwoEndedShift.symbolOp_apply_single_apply
#audit_axioms GroupApproximation.TwoEndedShift.symbol_mul
#audit_axioms GroupApproximation.TwoEndedShift.exists_tail_pos
#audit_axioms GroupApproximation.TwoEndedShift.exists_tail_translation_pos
#audit_axioms GroupApproximation.TwoEndedShift.exists_tail_translation_neg
