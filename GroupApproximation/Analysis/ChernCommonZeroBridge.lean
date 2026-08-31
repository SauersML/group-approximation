import GroupApproximation.Analysis.ChernCompressionMatrix
import GroupApproximation.Topology.TautologicalLineWinding

/-!
# From a common zero of the lower-left sections to the compression bound

`GroupApproximation.Analysis.ChernCompressionMatrix` proves the finite-dimensional
half of Section 2 of the STW Problem XXII audit: once the lower-left column of
every `z_j` vanishes at a single fibre, the operator norm of
`h - Σ_j [z_j*, z_j]` is at least one.  Its docstring says the only remaining
geometric input is "the common-zero property for the lower-left bundle
sections".  `GroupApproximation.Topology.TautologicalCommonZero` states exactly
that property, and this file joins the two.

The audit's blocks are `E_s = 1 ⊕ L_s^{⊕s}` over `ℂP^(s²)`, so relative to that
splitting a fibrewise endomorphism has a distinguished index `i₀` -- the trivial
line -- and its `i₀`-column off the diagonal is a section of `L_s^{⊕s}`.
`ColumnData` records precisely that link, and nothing else about the block.

## Main results

* `column_eq_zero_of_zero` -- a common zero of the column sections is exactly
  the hypothesis `hcol` of `ChernCompressionMatrix`.
* `exists_norm_sub_sum_selfCommutator_ge_one` -- the audit's inequality (A2),
  conditional on `CommonZeroProperty`.
* `exists_norm_sub_sum_selfCommutator_ge_one_of_subsingleton` -- the same
  inequality *unconditionally* for the `s = ℓ = 1` block, using the winding
  theorem of `TautologicalLineWinding`.
-/

namespace GroupApproximation
namespace ChernCommonZeroBridge

open TautologicalCommonZero
open CuntzPedersenCoronaObstruction
open scoped Matrix.Norms.L2Operator

/-- The link between a fibrewise family of block matrices and the sections of
the tautological sum that its distinguished column carries.

`mat j z` is the `j`-th endomorphism read at the homogeneous coordinate `z`;
`i₀` is the trivial-line index; and `column_eq` says that the `i₀`-column of
`mat j`, off the index `i₀` itself, is the section `sec j`. -/
structure ColumnData (N : ℕ) (ι : Type*) (i₀ : ι) (m : ℕ) where
  /-- The fibrewise block matrices. -/
  mat : Fin m → (Fin (N + 1) → ℂ) → Matrix ι ι ℂ
  /-- The lower-left column, read as a section of the tautological sum. -/
  sec : Fin m → TautSection N {i : ι // i ≠ i₀}
  /-- The two agree. -/
  column_eq : ∀ (j : Fin m) (z : Fin (N + 1) → ℂ) (i : {i : ι // i ≠ i₀}),
      mat j z (i : ι) i₀ = (sec j).toFun z i

/-- A common zero of the column sections is exactly the hypothesis `hcol` of
`ChernCompressionMatrix.norm_sub_sum_selfCommutator_ge_one`. -/
theorem column_eq_zero_of_zero {N : ℕ} {ι : Type*} {i₀ : ι} {m : ℕ}
    (D : ColumnData N ι i₀ m) {z : Fin (N + 1) → ℂ}
    (hz : ∀ j, (D.sec j).toFun z = 0) :
    ∀ (j : Fin m) (i : ι), i ≠ i₀ → D.mat j z i i₀ = 0 := by
  intro j i hi
  have hcol : D.mat j z i i₀ = (D.sec j).toFun z ⟨i, hi⟩ := D.column_eq j z ⟨i, hi⟩
  rw [hcol, hz j, Pi.zero_apply]

/-- The audit's inequality (A2) at one fibre. -/
theorem norm_sub_sum_selfCommutator_ge_one_of_zero
    {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {i₀ : ι} {m : ℕ}
    (D : ColumnData N ι i₀ m) (H : Matrix ι ι ℂ) (hdiag : H i₀ i₀ = 1)
    {z : Fin (N + 1) → ℂ} (hz : ∀ j, (D.sec j).toFun z = 0) :
    1 ≤ ‖H - ∑ j, selfCommutator (D.mat j z)‖ :=
  ChernCompressionMatrix.norm_sub_sum_selfCommutator_ge_one H (fun j => D.mat j z) i₀
    hdiag (column_eq_zero_of_zero D hz)

/-- **The audit's Section 2 lemma**, conditional on the Chern-class input.  If
the number of blocks times the rank of the tautological sum is at most the
complex dimension, some fibre of `H - Σ_j [z_j*, z_j]` has operator norm at
least one. -/
theorem exists_norm_sub_sum_selfCommutator_ge_one
    (hprop : CommonZeroProperty)
    {N : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {i₀ : ι} {m : ℕ}
    (hle : m * Nat.card {i : ι // i ≠ i₀} ≤ N)
    (D : ColumnData N ι i₀ m) (H : Matrix ι ι ℂ) (hdiag : H i₀ i₀ = 1) :
    ∃ z : Fin (N + 1) → ℂ, z ≠ 0 ∧
      1 ≤ ‖H - ∑ j, selfCommutator (D.mat j z)‖ := by
  have hle' : Nat.card (Fin m) * Nat.card {i : ι // i ≠ i₀} ≤ N := by
    rw [Nat.card_fin]
    exact hle
  obtain ⟨z, hz0, hz⟩ := hasCommonZero_of_property' hprop hle' D.sec
  exact ⟨z, hz0, norm_sub_sum_selfCommutator_ge_one_of_zero D H hdiag hz⟩

/-- The same inequality with **no** Chern-class hypothesis, in the rank-one
corner: one block (`Fin m` a subsingleton, so `m ≤ 1`) and a two-dimensional
fibre (`{i // i ≠ i₀}` a subsingleton).  This is the `s = ℓ = 1` block of the
counterexample, and it rests only on `TautologicalLineWinding`. -/
theorem exists_norm_sub_sum_selfCommutator_ge_one_of_subsingleton
    {N : ℕ} (hN : 1 ≤ N) {ι : Type*} [Fintype ι] [DecidableEq ι] {i₀ : ι} {m : ℕ}
    [Subsingleton (Fin m)] [Subsingleton {i : ι // i ≠ i₀}]
    (D : ColumnData N ι i₀ m) (H : Matrix ι ι ℂ) (hdiag : H i₀ i₀ = 1) :
    ∃ z : Fin (N + 1) → ℂ, z ≠ 0 ∧
      1 ≤ ‖H - ∑ j, selfCommutator (D.mat j z)‖ := by
  obtain ⟨z, hz0, hz⟩ :=
    TautologicalLineWinding.hasCommonZero_of_subsingleton hN D.sec
  exact ⟨z, hz0, norm_sub_sum_selfCommutator_ge_one_of_zero D H hdiag hz⟩

end ChernCommonZeroBridge
end GroupApproximation
