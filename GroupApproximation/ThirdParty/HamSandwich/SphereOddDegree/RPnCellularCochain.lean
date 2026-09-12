import Mathlib
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnCellularFiltration

/-!
# Cellular cochain groups of `RPⁿ` over `F₂ = ZMod 2`

Building on the cellular filtration of `RPⁿ` from `RPnCellularFiltration.lean`
(one cell in each dimension `0 … n`, none above), this file defines the
**cellular cochain groups** of `RPⁿ` over `ZMod 2` and proves that each cochain
group is one-dimensional for `0 ≤ k ≤ n` and zero above `n`.

## Model

The cellular chain group in degree `k` over `F₂` is the free `F₂`-module on the
set of `k`-cells `RPn.cellIndex n k`, and the cochain group is its dual.  Since
the cell set is a singleton for `k ≤ n` (and empty above), we model the cochain
group directly as the function space

```text
RPn.cellCochain n k = (RPn.cellIndex n k → ZMod 2),
```

which, as an `F₂`-vector space, is one-dimensional for `k ≤ n` and zero
dimensional above `n`.

## What is built

* `RPn.cellCochain n k` — the cellular cochain group, with its `F₂`-module
  structure.
* `RPn.rpCellCochainBasis n k` — the canonical basis cochain `uₖ` with
  `uₖ(eₖ) = 1` on the unique `k`-cell.
* `RPn.rpCellCochainBasis_ne_zero` — `uₖ ≠ 0` for `k ≤ n`.
* `RPn.rpCellCochain_spans` — every cochain is a scalar multiple of `uₖ` for
  `k ≤ n`.
* `RPn.rpCellCochain_subsingleton_of_gt` / `RPn.rpCellCochain_eq_zero_of_gt` —
  the cochain group is zero above `n`.
-/

noncomputable section

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
namespace RPn

/-! ## Algebraic lemmas over `ZMod 2` -/

/-- A `ZMod 2`-valued function on a (nonempty) subsingleton type is constant:
it equals `fun _ => a` for the scalar `a` it takes on the unique point. -/
theorem zmod2_scalar_of_singleton_function
    {A : Type} [Subsingleton A] [Nonempty A]
    (x : A → ZMod 2) :
    ∃ a : ZMod 2, x = fun _ => a := by
  obtain ⟨p⟩ := ‹Nonempty A›
  refine ⟨x p, ?_⟩
  funext q
  rw [Subsingleton.elim q p]

/-- The constant-`1` function on a nonempty type is nonzero. -/
theorem singleton_function_basis_ne_zero
    {A : Type} [Nonempty A] :
    (fun _ : A => (1 : ZMod 2)) ≠ 0 := by
  obtain ⟨p⟩ := ‹Nonempty A›
  intro h
  have : (1 : ZMod 2) = 0 := congrFun h p
  exact one_ne_zero this

/-! ## The cellular cochain group -/

/-- The **cellular cochain group** of `RPⁿ` in degree `k` over `F₂ = ZMod 2`:
the dual of the free `F₂`-module on the `k`-cells, modelled directly as the
function space on the (singleton, resp. empty) set of `k`-cells. -/
def cellCochain (n k : ℕ) : Type := cellIndex n k → ZMod 2

instance instAddCommGroupCellCochain (n k : ℕ) : AddCommGroup (cellCochain n k) := by
  unfold cellCochain; infer_instance

instance instModuleCellCochain (n k : ℕ) : Module (ZMod 2) (cellCochain n k) := by
  unfold cellCochain; infer_instance

/-- The canonical basis cochain `uₖ`, defined by evaluation `uₖ(eₖ) = 1` on the
unique `k`-cell. -/
def rpCellCochainBasis (n k : ℕ) : cellCochain n k := fun _ => 1

/-- The basis cochain `uₖ` is nonzero for `k ≤ n` (where there is a `k`-cell). -/
theorem rpCellCochainBasis_ne_zero {n k : ℕ} (hk : k ≤ n) :
    rpCellCochainBasis n k ≠ 0 := by
  haveI : Nonempty (cellIndex n k) := cellIndex_nonempty hk
  exact singleton_function_basis_ne_zero

/-- The basis cochain `uₖ` spans the cochain group for `k ≤ n`: every cochain is
a scalar multiple of `uₖ`. -/
theorem rpCellCochain_spans {n k : ℕ} (hk : k ≤ n) (x : cellCochain n k) :
    ∃ a : ZMod 2, x = a • rpCellCochainBasis n k := by
  haveI : Nonempty (cellIndex n k) := cellIndex_nonempty hk
  haveI : Subsingleton (cellIndex n k) := instSubsingletonCellIndex n k
  obtain ⟨a, ha⟩ := zmod2_scalar_of_singleton_function (A := cellIndex n k) x
  refine ⟨a, ?_⟩
  rw [ha]
  funext q
  show a = a • (rpCellCochainBasis n k q)
  simp only [rpCellCochainBasis, smul_eq_mul, mul_one]

/-- Above the top dimension `n`, the cochain group is a subsingleton (there are
no `k`-cells). -/
theorem rpCellCochain_subsingleton_of_gt {n k : ℕ} (hk : n < k) :
    Subsingleton (cellCochain n k) := by
  haveI : IsEmpty (cellIndex n k) := cellIndex_empty_of_gt hk
  unfold cellCochain
  infer_instance

/-- Above the top dimension `n`, every cochain is zero. -/
theorem rpCellCochain_eq_zero_of_gt {n k : ℕ} (hk : n < k)
    (x : cellCochain n k) : x = 0 := by
  haveI := rpCellCochain_subsingleton_of_gt hk
  exact Subsingleton.elim x 0

end RPn
end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

