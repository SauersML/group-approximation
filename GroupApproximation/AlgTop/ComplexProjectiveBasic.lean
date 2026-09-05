import GroupApproximation.Analysis.LIXProjectiveSpaceModel

/-!
# Entry calculus on the projection model of `ℂP^d`

The model itself lives in `GroupApproximation/Analysis/LIXProjectiveSpaceModel.lean`
(lane `lix-spaces`): `STW59.cpSet d` is the set of rank-one orthogonal projections in
`M_{d+1}(ℂ)` and `STW59.CP d = ↥(STW59.cpSet d)` carries the subspace topology of the
product topology on matrices. **This file adds no competing model.**

What it adds is the entrywise calculus that the cell structure of `ℂP^d` runs on. The
single fact everything downstream uses is the vanishing of the `2 × 2` minors,

```text
CPn.minor : q a j * q j b = q j j * q a b,
```

which says exactly that `q` has rank one. It follows in one step from
`STW59.eq_rankOneProj_of_trace_one`, and unlike that existential statement it is directly
usable as a rewrite: on the locus `q j j ≠ 0` it recovers every entry of `q` from its
`j`-th column and row.

## Main results

* `CPn.minor`, `CPn.sum_mul` — the rank-one and idempotent identities, entrywise;
* `CPn.col_eq_zero_of_diag_eq_zero`, `CPn.row_eq_zero_of_diag_eq_zero` — a vanishing
  diagonal entry kills its whole column and row;
* `CPn.entry` and `CPn.continuous_entry` — entry evaluation `ℂP^d → ℂ`, and its
  continuity, the workhorse of every later topology proof.

## Index convention

`CP d` is complex projective `d`-space: `CP 0` is a point and `CP d` has real dimension
`2d`. This is the convention of the campaign manuscript
(`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md` §2),
where `Y = ∏ⱼ ℂP^{dⱼ}` has `H^{2m}(Y;ℤ) ≅ ℤ` for `m = ∑ⱼ dⱼ`.
-/

noncomputable section

namespace GroupApproximation.AlgTop

open Matrix
open GroupApproximation.STW59

namespace CPn

variable {d : ℕ}

/-! ## 1. Entrywise identities for rank-one projections -/

section Entrywise

variable {n : Type*} [Fintype n] {q : Matrix n n ℂ}

/-- The idempotent law, read off entrywise. -/
theorem sum_mul (hq : IsStarProjection q) (x y : n) : (∑ c, q x c * q c y) = q x y := by
  have h := Matrix.mul_apply (M := q) (N := q) (i := x) (j := y)
  rw [hq.isIdempotentElem.eq] at h
  exact h.symm

/-- If a diagonal entry of a projection vanishes, so does the whole corresponding
column. -/
theorem col_eq_zero_of_diag_eq_zero (hq : IsStarProjection q) {j : n} (hj : q j j = 0)
    (c : n) : q c j = 0 := by
  have h1 : ((∑ k, ‖q k j‖ ^ 2 : ℝ) : ℂ) = ((0 : ℝ) : ℂ) := by
    rw [← proj_diag_eq hq j, hj, Complex.ofReal_zero]
  have h2 : (∑ k, ‖q k j‖ ^ 2 : ℝ) = 0 := by exact_mod_cast h1
  have h3 : ‖q c j‖ ^ 2 = 0 :=
    le_antisymm (h2 ▸ Finset.single_le_sum (fun k _ => by positivity) (Finset.mem_univ c))
      (by positivity)
  have h4 : ‖q c j‖ = 0 := by nlinarith [norm_nonneg (q c j)]
  simpa using h4

/-- If a diagonal entry of a projection vanishes, so does the whole corresponding row. -/
theorem row_eq_zero_of_diag_eq_zero (hq : IsStarProjection q) {j : n} (hj : q j j = 0)
    (c : n) : q j c = 0 := by
  rw [proj_entry_symm hq j c, col_eq_zero_of_diag_eq_zero hq hj c, star_zero]

end Entrywise

/-- **Rank one, as the vanishing of every `2 × 2` minor.** For a rank-one projection,
`q a j * q j b = q j j * q a b`.

On `{q j j ≠ 0}` this recovers every entry from the `j`-th column and row, which is what
makes the affine chart of `ℂP^d` a rational function of the coordinates. -/
theorem minor {q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ} (hq : q ∈ cpSet d)
    (a b j : Fin (d + 1)) : q a j * q j b = q j j * q a b := by
  obtain ⟨x, _, rfl⟩ :=
    eq_rankOneProj_of_trace_one (isStarProjection_of_mem_cpSet hq) (trace_of_mem_cpSet hq)
  simp only [rankOneProj_apply]
  ring

/-! ## 2. Points of `CP d` as matrices -/

/-- The `(a, b)` entry of the projection naming a point of `ℂP^d`. -/
abbrev entry (x : CP d) (a b : Fin (d + 1)) : ℂ :=
  (x : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) a b

theorem isStarProjection_coe (x : CP d) :
    IsStarProjection (x : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :=
  isStarProjection_of_mem_cpSet x.2

theorem trace_coe (x : CP d) : (x : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ).trace = 1 :=
  trace_of_mem_cpSet x.2

theorem entry_symm (x : CP d) (a b : Fin (d + 1)) : entry x a b = star (entry x b a) :=
  proj_entry_symm (isStarProjection_coe x) a b

/-- Conjugation of entries, in the `starRingEnd` form that `map_mul` / `map_div₀`
produce after distributing `conj` over a quotient of products. -/
theorem entry_conj (x : CP d) (a b : Fin (d + 1)) :
    (starRingEnd ℂ) (entry x b a) = entry x a b := by
  rw [← Complex.star_def]
  exact (entry_symm x a b).symm

theorem entry_minor (x : CP d) (a b j : Fin (d + 1)) :
    entry x a j * entry x j b = entry x j j * entry x a b :=
  minor x.2 a b j

theorem entry_sum_mul (x : CP d) (a b : Fin (d + 1)) :
    (∑ c, entry x a c * entry x c b) = entry x a b :=
  sum_mul (isStarProjection_coe x) a b

theorem entry_diag (x : CP d) (j : Fin (d + 1)) :
    entry x j j = ((∑ k, ‖entry x k j‖ ^ 2 : ℝ) : ℂ) :=
  proj_diag_eq (isStarProjection_coe x) j

theorem entry_col_eq_zero (x : CP d) {j : Fin (d + 1)} (hj : entry x j j = 0)
    (c : Fin (d + 1)) : entry x c j = 0 :=
  col_eq_zero_of_diag_eq_zero (isStarProjection_coe x) hj c

theorem entry_row_eq_zero (x : CP d) {j : Fin (d + 1)} (hj : entry x j j = 0)
    (c : Fin (d + 1)) : entry x j c = 0 :=
  row_eq_zero_of_diag_eq_zero (isStarProjection_coe x) hj c

theorem ext {x y : CP d} (h : ∀ a b, entry x a b = entry y a b) : x = y :=
  Subtype.ext (Matrix.ext h)

/-! ## 3. Continuity -/

theorem continuous_coe :
    Continuous fun x : CP d => (x : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :=
  continuous_subtype_val

theorem continuous_entry (a b : Fin (d + 1)) : Continuous fun x : CP d => entry x a b :=
  continuous_coe.matrix_elem a b

/-! ## 4. The base point -/

theorem basePoint_unit (d : ℕ) :
    (Pi.single (0 : Fin (d + 1)) (1 : ℂ)) ∈ unitVectors (d + 1) := by
  show (∑ i, ‖(Pi.single (0 : Fin (d + 1)) (1 : ℂ)) i‖ ^ 2) = 1
  rw [Finset.sum_eq_single (0 : Fin (d + 1))]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin (d + 1))) h

/-- The base point `[1 : 0 : ⋯ : 0]` of `ℂP^d`, i.e. the projection onto the first
coordinate axis. -/
def basePoint (d : ℕ) : CP d :=
  ⟨rankOneProj (Pi.single 0 1), rankOneProj_mem_cpSet (basePoint_unit d)⟩

theorem basePoint_entry (d : ℕ) (a b : Fin (d + 1)) :
    entry (basePoint d) a b =
      (Pi.single (0 : Fin (d + 1)) (1 : ℂ)) a * star ((Pi.single (0 : Fin (d + 1)) (1 : ℂ)) b) :=
  rfl

@[simp] theorem basePoint_entry_zero_zero (d : ℕ) : entry (basePoint d) 0 0 = 1 := by
  rw [basePoint_entry]
  simp

end CPn

end GroupApproximation.AlgTop
