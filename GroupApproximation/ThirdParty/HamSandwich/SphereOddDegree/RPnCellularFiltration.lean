import Mathlib
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnFiltrationCofiber
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnAdditiveCohomology

/-!
# The cellular filtration of `RPⁿ`

This file exposes the standard **cellular filtration** of real projective space

```text
RP⁰ ⊂ RP¹ ⊂ ⋯ ⊂ RPⁿ
```

with **exactly one cell in every dimension `0, 1, …, n`** and **no cells above
`n`**, packaged as a concrete data certificate and connected to the project's
cellular cochain model `rpCellularCochainComplex n` (`RPnAdditiveCohomology.lean`).

## Geometric content

`RPᵏ = Sᵏ / (x ~ −x)` (`RP k`, `RealProjectiveSpace.lean`); the equatorial
inclusions `RPᵏ ↪ RPᵏ⁺¹` (`rpInclusion`, `RealProjectiveSpaceInclusion.lean`)
assemble into the filtration functor `rpFiltration : ℕ ⥤ TopCat`
(`RPnFiltrationCofiber.lean`). The closed upper hemisphere `H⁺ ⊂ Sᵏ` is a closed
`k`-disk whose interior maps injectively into `RPᵏ` (one representative per
antipodal pair with positive last coordinate) and whose boundary equatorial
sphere `Sᵏ⁻¹` attaches along the quotient map `Sᵏ⁻¹ → RPᵏ⁻¹`. Hence

```text
RPᵏ = RPᵏ⁻¹ ∪_{Sᵏ⁻¹ → RPᵏ⁻¹} Dᵏ,
```

a single `k`-cell in each dimension, recorded combinatorially below.

## What is built

* `RPn.skeleton n k` — the `k`-skeleton `RPᵏ` (`= RP k`), with the skeleton
  inclusions `RPn.skeletonIncl : k ≤ n → RPᵏ → RPⁿ` taken from the project's
  filtration functor.
* `RPn.cellIndex n k` — the (combinatorial) set of `k`-cells of `RPⁿ`: a single
  cell for `k ≤ n`, empty above, with
  `RPn.cellIndex_nonempty`, `RPn.cellIndex_unique` (subsingleton), and
  `RPn.cellIndex_empty_of_gt`, plus `RPn.cellIndex_unique'` (`Unique` for
  `k ≤ n`).
* `RPn.cellularBasis n k` — the **connection to the cochain model**: an explicit
  `ZMod 2`-basis of the cellular cochain object `rpCellularX n k` indexed by the
  `k`-cells `RPn.cellIndex n k`. So `rpCellularX n k` is the free `F₂`-module on
  the `k`-cells: one basis element in each degree `k ≤ n`, none above. The
  corresponding `RPn.cellIndex_card` records `#cells = dim`.
* `RPnCellularFiltration n` / `RPn.filtration n` — the certificate packaging the
  skeleton, the cell-index data, and the cochain basis together.
-/

noncomputable section

open CategoryTheory

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
namespace RPn

/-! ## 1. Skeleta and skeleton inclusions -/

/-- The `k`-skeleton of the cellular filtration of `RPⁿ`: the projective space
`RPᵏ`. For `k ≤ n` it sits inside `RPⁿ` via the equatorial inclusions. -/
def skeleton (n k : ℕ) : Type := RP k

@[simp] theorem skeleton_eq (n k : ℕ) : skeleton n k = RP k := rfl

instance (n k : ℕ) : TopologicalSpace (skeleton n k) := by
  unfold skeleton; infer_instance

/-- The skeleton inclusion `RPᵏ → RPⁿ` for `k ≤ n`, taken from the project's
filtration functor `rpFiltration : ℕ ⥤ TopCat`. -/
def skeletonIncl {n k : ℕ} (hk : k ≤ n) : skeleton n k → skeleton n n :=
  fun x => (rpFiltration.map (homOfLE hk)).hom x

/-- The single-step skeleton inclusion is the equatorial inclusion `rpInclusion`. -/
theorem skeletonIncl_succ {n : ℕ} :
    skeletonIncl (n := n + 1) (k := n) (Nat.le_succ n)
      = fun x => rpInclusion n x := by
  funext x
  show (rpFiltration.map (homOfLE (Nat.le_succ n))).hom x = _
  rw [rpFiltration_map_succ]
  rfl

/-! ## 2. The cells of `RPⁿ`: one in each degree `0 … n`, none above -/

/-- The set of `k`-cells of `RPⁿ`: a single cell in each degree `0 ≤ k ≤ n`,
empty above `n`. -/
def cellIndex (n k : ℕ) : Type := if k ≤ n then PUnit else PEmpty

instance (n k : ℕ) : Fintype (cellIndex n k) := by
  unfold cellIndex; split <;> infer_instance

instance instSubsingletonCellIndex (n k : ℕ) : Subsingleton (cellIndex n k) := by
  unfold cellIndex; split <;> infer_instance

/-- There is at least one `k`-cell whenever `k ≤ n`. -/
theorem cellIndex_nonempty {n k : ℕ} (hk : k ≤ n) : Nonempty (cellIndex n k) := by
  unfold cellIndex; rw [if_pos hk]; exact ⟨PUnit.unit⟩

/-- The set of `k`-cells is a subsingleton: at most one `k`-cell in every
degree. (The hypothesis `hk : k ≤ n` is requested by the cellular-filtration
interface; it turns out to be unnecessary, since `cellIndex n k` is a
subsingleton in every degree — see `instSubsingletonCellIndex`.) -/
theorem cellIndex_unique {n k : ℕ} (hk : k ≤ n) : Subsingleton (cellIndex n k) :=
  instSubsingletonCellIndex n k

/-- There is **exactly one** `k`-cell whenever `k ≤ n`. -/
def cellIndex_unique' {n k : ℕ} (hk : k ≤ n) : Unique (cellIndex n k) :=
  haveI := instSubsingletonCellIndex n k
  uniqueOfSubsingleton (cellIndex_nonempty hk).some

/-- There are **no** `k`-cells above the dimension: `k > n` gives an empty cell
set. -/
theorem cellIndex_empty_of_gt {n k : ℕ} (hk : n < k) : IsEmpty (cellIndex n k) := by
  unfold cellIndex; rw [if_neg (by omega)]; infer_instance

/-! ## 3. Connection to the cellular cochain model -/

/-- **The cellular cochain object is the free `F₂`-module on the `k`-cells.** An
explicit `ZMod 2`-basis of `rpCellularX n k` (the degree-`k` object of the
cellular cochain complex of `RPⁿ`) indexed by the set of `k`-cells
`RPn.cellIndex n k`. There is one basis element in each degree `k ≤ n` and none
above `n`. -/
def cellularBasis (n k : ℕ) :
    Module.Basis (cellIndex n k) (ZMod 2) (rpCellularX n k) := by
  by_cases hk : k ≤ n
  · have hc : cellIndex n k = PUnit := by unfold cellIndex; exact if_pos hk
    exact ((Module.Basis.singleton PUnit (ZMod 2)).map
      (rpCellularX_iso_in_range n k hk).toLinearEquiv.symm).reindex (Equiv.cast hc).symm
  · haveI : IsEmpty (cellIndex n k) := cellIndex_empty_of_gt (by omega)
    haveI : Subsingleton (rpCellularX n k) := by
      unfold rpCellularX; rw [if_neg hk]; infer_instance
    exact Module.Basis.empty _

/-- The number of `k`-cells equals the `F₂`-dimension of the degree-`k` cellular
cochain object. -/
theorem cellIndex_card (n k : ℕ) :
    Fintype.card (cellIndex n k) = Module.finrank (ZMod 2) (rpCellularX n k) := by
  rw [Module.finrank_eq_card_basis (cellularBasis n k)]

end RPn

/-! ## 4. The cellular-filtration certificate -/

/-- A certificate that `RPⁿ` carries the standard cellular filtration with
exactly one cell in each dimension `0 … n` and none above, together with the
identification of each cellular cochain group with the free `F₂`-module on the
cells of that degree. -/
structure RPnCellularFiltration (n : ℕ) where
  /-- The `k`-skeleton. -/
  skeleton : ℕ → Type
  /-- Inclusion of the `k`-skeleton into the top skeleton for `k ≤ n`. -/
  skeletonIncl : ∀ k, k ≤ n → skeleton k → skeleton n
  /-- The set of `k`-cells. -/
  cellIndex : ℕ → Type
  /-- There is at least one `k`-cell for `k ≤ n`. -/
  cellIndex_nonempty : ∀ k, k ≤ n → Nonempty (cellIndex k)
  /-- There is at most one `k`-cell in every degree. -/
  cellIndex_subsingleton : ∀ k, Subsingleton (cellIndex k)
  /-- There are no cells above the dimension `n`. -/
  no_cells_above : ∀ k, n < k → IsEmpty (cellIndex k)
  /-- Each cellular cochain group `rpCellularX n k` is the free `F₂`-module on the
  `k`-cells. -/
  cochainBasis : ∀ k, Module.Basis (cellIndex k) (ZMod 2) (rpCellularX n k)

/-- **The standard cellular filtration of `RPⁿ`.** A concrete
`RPnCellularFiltration n` built from the project's projective skeleta, equatorial
inclusions, and cellular cochain model: one cell in each dimension `0 … n`, none
above, with each cochain group free of rank one (resp. zero) on the cells. -/
def RPn.filtration (n : ℕ) : RPnCellularFiltration n where
  skeleton := fun k => RPn.skeleton n k
  skeletonIncl := fun _ hk => RPn.skeletonIncl hk
  cellIndex := fun k => RPn.cellIndex n k
  cellIndex_nonempty := fun _ hk => RPn.cellIndex_nonempty hk
  cellIndex_subsingleton := fun k => RPn.instSubsingletonCellIndex n k
  no_cells_above := fun _ hk => RPn.cellIndex_empty_of_gt hk
  cochainBasis := fun k => RPn.cellularBasis n k

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

