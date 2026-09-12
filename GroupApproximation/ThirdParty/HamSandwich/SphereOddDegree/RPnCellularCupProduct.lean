import Mathlib
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnCellularCochain

/-!
# The model-side cellular cup product of `RPⁿ` over `F₂ = ZMod 2`

Building on the cellular cochain model from `RPnCellularCochain.lean` (one cell
in each dimension `0 … n`, cochain group `cellCochain n k = cellIndex n k →
ZMod 2` one-dimensional for `k ≤ n` and zero above), this file defines the
**model-side cellular cup product**

```text
uₚ ∪cell u_q = u_{p+q}   if p + q ≤ n,
uₚ ∪cell u_q = 0         if p + q > n.
```

This is *only* the model-side multiplication; it does not yet claim agreement
with the singular cup product `cupZMod2`.  That comparison is a later prompt.

## What is built

* `RPn.cellCoeff` — the scalar coefficient of a cochain on the unique cell in an
  in-range degree.
* `RPn.cellCup` — the cellular cup product as an `F₂`-bilinear map.
* `RPn.cellCup_basis` — sends basis cochains to basis cochains in range.
* `RPn.cellCup_eq_zero_of_sum_gt` — vanishes above the top dimension.
* `RPn.cellCup_smul_left` / `..._smul_right` / `..._add_left` / `..._add_right`
  — bilinearity (immediate from the `LinearMap` structure).
-/

noncomputable section

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
namespace RPn

/-- The scalar coefficient of a cellular cochain `a` on the unique `k`-cell,
when `k ≤ n`; otherwise `0` (the cochain group is then zero). -/
noncomputable def cellCoeff (n k : ℕ) (a : cellCochain n k) : ZMod 2 :=
  if h : k ≤ n then a (cellIndex_nonempty h).some else 0

theorem cellCoeff_add (n k : ℕ) (a a' : cellCochain n k) :
    cellCoeff n k (a + a') = cellCoeff n k a + cellCoeff n k a' := by
  unfold cellCoeff
  by_cases h : k ≤ n
  · simp [h]; rfl
  · simp [h]

theorem cellCoeff_smul (n k : ℕ) (c : ZMod 2) (a : cellCochain n k) :
    cellCoeff n k (c • a) = c * cellCoeff n k a := by
  unfold cellCoeff
  by_cases h : k ≤ n
  · simp [h]; rfl
  · simp [h]

/-- The coefficient of the basis cochain `uₖ` on the unique cell is `1` for
`k ≤ n`. -/
theorem cellCoeff_basis (n k : ℕ) (hk : k ≤ n) :
    cellCoeff n k (rpCellCochainBasis n k) = 1 := by
  unfold cellCoeff rpCellCochainBasis
  simp [hk]

/-- The **cellular cup product** of `RPⁿ` over `F₂`, as an `F₂`-bilinear map. -/
noncomputable def cellCup (n p q : ℕ) :
    cellCochain n p →ₗ[ZMod 2]
      cellCochain n q →ₗ[ZMod 2]
        cellCochain n (p + q) :=
  LinearMap.mk₂ (ZMod 2)
    (fun a b =>
      if h : p + q ≤ n then
        (cellCoeff n p a * cellCoeff n q b) • rpCellCochainBasis n (p + q)
      else 0)
    (by
      intro a a' b
      by_cases h : p + q ≤ n
      · simp only [h, dif_pos]
        rw [cellCoeff_add, add_mul, add_smul]
      · simp [h])
    (by
      intro c a b
      by_cases h : p + q ≤ n
      · simp only [h, dif_pos]
        rw [cellCoeff_smul, mul_assoc, mul_smul]
      · simp [h])
    (by
      intro a b b'
      by_cases h : p + q ≤ n
      · simp only [h, dif_pos]
        rw [cellCoeff_add, mul_add, add_smul]
      · simp [h])
    (by
      intro c a b
      by_cases h : p + q ≤ n
      · simp only [h, dif_pos]
        rw [cellCoeff_smul, mul_left_comm, mul_smul]
      · simp [h])

theorem cellCup_apply (n p q : ℕ) (a : cellCochain n p) (b : cellCochain n q) :
    cellCup n p q a b =
      if _h : p + q ≤ n then
        (cellCoeff n p a * cellCoeff n q b) • rpCellCochainBasis n (p + q)
      else 0 := rfl

theorem cellCup_basis
    (n : ℕ) {p q : ℕ} (hp : p ≤ n) (hq : q ≤ n) (hpq : p + q ≤ n) :
    cellCup n p q
      (rpCellCochainBasis n p)
      (rpCellCochainBasis n q)
    = rpCellCochainBasis n (p + q) := by
  rw [cellCup_apply]
  simp [hpq, cellCoeff_basis n p hp, cellCoeff_basis n q hq]

theorem cellCup_eq_zero_of_sum_gt
    (n : ℕ) {p q : ℕ} (hgt : n < p + q)
    (a : cellCochain n p) (b : cellCochain n q) :
    cellCup n p q a b = 0 := by
  rw [cellCup_apply]
  rw [dif_neg (by omega)]

theorem cellCup_smul_left
    (n p q : ℕ) (c : ZMod 2) (a : cellCochain n p) (b : cellCochain n q) :
    cellCup n p q (c • a) b = c • cellCup n p q a b := by
  rw [map_smul, LinearMap.smul_apply]

theorem cellCup_smul_right
    (n p q : ℕ) (c : ZMod 2) (a : cellCochain n p) (b : cellCochain n q) :
    cellCup n p q a (c • b) = c • cellCup n p q a b := by
  rw [map_smul]

theorem cellCup_add_left
    (n p q : ℕ) (a a' : cellCochain n p) (b : cellCochain n q) :
    cellCup n p q (a + a') b = cellCup n p q a b + cellCup n p q a' b := by
  rw [map_add, LinearMap.add_apply]

theorem cellCup_add_right
    (n p q : ℕ) (a : cellCochain n p) (b b' : cellCochain n q) :
    cellCup n p q a (b + b') = cellCup n p q a b + cellCup n p q a b' := by
  rw [map_add]

end RPn
end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

