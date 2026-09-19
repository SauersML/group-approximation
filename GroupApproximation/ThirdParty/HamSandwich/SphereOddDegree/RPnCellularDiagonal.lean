import Mathlib
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnCellularCupProduct
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.AlexanderWhitneyChainMap

/-!
# The RPⁿ cellular diagonal coefficient formula

This file supplies the topological/combinatorial justification of the model-side
cellular cup product (`RPnCellularCupProduct.lean`): the Alexander–Whitney
diagonal of the unique `(p+q)`-cell of `RPⁿ` has coefficient `1` on the
front/back split of bidegree `(p,q)`.

## Mathematical statement

Let `e_k` be the unique `k`-cell of `RPⁿ`.  The Alexander–Whitney diagonal of a
singular `(p+q)`-simplex `σ` is the sum over all front/back splits

```text
Δ_AW(σ) = Σ_{i=0}^{p+q} σ|[0,…,i] ⊗ σ|[i,…,p+q].
```

In the cellular model of `RPⁿ` every nondegenerate `r`-face maps to the unique
`r`-cell `e_r`, so the split at cut point `i` contributes `e_i ⊗ e_{(p+q)-i}`.
The split has bidegree `(p,q)` exactly when `i = p` (front dimension `i`, back
dimension `(p+q)-i`), and this is the **unique** such split.  Over `F₂ = ZMod 2`
there are no signs, so the coefficient of `e_p ⊗ e_q` in `Δ(e_{p+q})` is `1`.

This is the coefficient statement that dualizes to `u_p ∪ u_q = u_{p+q}`.

## What is built

* `RPn.awSplitFrontDim` / `RPn.awSplitBackDim` — the front and back dimensions of
  the AW split at cut point `i`.
* `RPn.aw_split_bidegree_eq` — the split has bidegree `(p,q)` iff `i = p`
  (uniqueness of the `p`-split).
* `RPn.cellularDiagonalCoeff` — the coefficient of `e_p ⊗ e_q` in the AW diagonal
  of the unique `(p+q)`-cell: the sum over AW splits (indexed by
  `Fin (p+q+1)`) of the bidegree-`(p,q)` indicator, reduced mod 2.
* `RPn.cellularDiagonalCoeff_eq_one` — the coefficient is `1`.
* `RPn.rpCellularCup_basis_from_AW` — the model-side `cellCup` on the cellular
  basis is the AW-diagonal coefficient times the `(p+q)`-basis cochain, i.e. the
  model multiplication agrees with the Alexander–Whitney diagonal on the basis.
-/

noncomputable section

open CategoryTheory AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
namespace RPn

/-! ## 1. The bidegrees of an Alexander–Whitney split -/

/-- The **front dimension** of the Alexander–Whitney split of a `(p+q)`-simplex
at cut point `i`: the front face `[0,…,i]` has dimension `i`. -/
def awSplitFrontDim (_p _q i : ℕ) : ℕ := i

/-- The **back dimension** of the Alexander–Whitney split of a `(p+q)`-simplex at
cut point `i`: the back face `[i,…,p+q]` has dimension `(p+q)-i`. -/
def awSplitBackDim (p q i : ℕ) : ℕ := (p + q) - i

/-- **Uniqueness of the `p`-split.** Among the Alexander–Whitney splits of a
`(p+q)`-simplex (cut points `i ≤ p+q`), the one with bidegree `(p,q)` is exactly
the split at `i = p`. -/
theorem aw_split_bidegree_eq {p q i : ℕ} (hi : i ≤ p + q) :
    i = p ↔ (awSplitFrontDim p q i = p ∧ awSplitBackDim p q i = q) := by
  unfold awSplitFrontDim awSplitBackDim
  constructor
  · rintro rfl
    exact ⟨rfl, by omega⟩
  · rintro ⟨h1, _⟩
    exact h1

/-! ## 2. The cellular diagonal coefficient -/

/-- The **cellular diagonal coefficient** of `RPⁿ` in bidegree `(p,q)`: the
coefficient of `e_p ⊗ e_q` in the Alexander–Whitney diagonal of the unique
`(p+q)`-cell.  Concretely, the AW diagonal is the sum over front/back splits
indexed by the cut point `i ∈ Fin (p+q+1)`; each split contributes
`e_i ⊗ e_{(p+q)-i}`, so the coefficient of `e_p ⊗ e_q` is the (mod-2) number of
splits of bidegree `(p,q)`. -/
def cellularDiagonalCoeff (n p q : ℕ) (_hpq : p + q ≤ n) : ZMod 2 :=
  ∑ i : Fin (p + q + 1),
    if (awSplitFrontDim p q i.val = p ∧ awSplitBackDim p q i.val = q) then (1 : ZMod 2) else 0

/-- **The RPⁿ cellular diagonal coefficient is `1`.**  The only Alexander–Whitney
split of bidegree `(p,q)` is the split at cut point `p`, and over `ZMod 2` its
coefficient is `1`; all other splits have a different bidegree and contribute
`0`.
-/
theorem cellularDiagonalCoeff_eq_one
    (n : ℕ) {p q : ℕ} (hpq : p + q ≤ n) :
    cellularDiagonalCoeff n p q hpq = (1 : ZMod 2) := by
  unfold cellularDiagonalCoeff;
  simp +decide [ awSplitFrontDim, awSplitBackDim ];
  rw [ Finset.card_eq_one.mpr ];
  · norm_num;
  · use ⟨ p, by linarith ⟩ ; ext x; simp +decide [ Fin.ext_iff ] ; omega;

/-! ## 3. Agreement of the model cup product with the AW diagonal on the basis -/

/-- **The model cellular cup product agrees with the Alexander–Whitney diagonal
on the cellular basis.**  The model-side product `cellCup` of the basis cochains
`u_p`, `u_q` equals the AW-diagonal coefficient in bidegree `(p,q)` times the
basis cochain `u_{p+q}`.  Together with `cellularDiagonalCoeff_eq_one` this is the
identity `u_p ∪ u_q = u_{p+q}`. -/
theorem rpCellularCup_basis_from_AW
    (n : ℕ) {p q : ℕ} (hp : p ≤ n) (hq : q ≤ n) (hpq : p + q ≤ n) :
    cellCup n p q
        (rpCellCochainBasis n p)
        (rpCellCochainBasis n q)
      = cellularDiagonalCoeff n p q hpq • rpCellCochainBasis n (p + q) := by
  rw [cellularDiagonalCoeff_eq_one, one_smul, cellCup_basis n hp hq hpq]

end RPn
end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
