import Mathlib
import GroupApproximation.Analysis.LIXProjectiveSpaceModel

/-!
# An explicit section of `L^{⊕d}` over `ℂP^d` with exactly one zero

Lane `lix-obstruction`, campaign target 3 (STW Problem LIX).

In the proof of Lemma 2 of
`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md`
one chooses "a smooth section `σ` of `H` transverse to zero", and the signed count of
its zeros is then read off from the Chern number

```text
|⟨c_m(H), [Y]⟩| = 1                                                       (2.1)
```

which the manuscript obtains from the cohomology ring of `Y = ∏_j ℂP^{d_j}`.

**That Chern computation is not needed.**  For `H = L^{⊕d}` over `ℂP^d` there is an
explicit section with exactly one zero, and the zero is visibly nondegenerate.  In the
rank-one-projection model of `ℂP^d` (`LIXProjectiveSpaceModel.lean`), a constant vector
`a ∈ ℂ^{d+1}` gives the section

```text
σ_a (z) = z a          (the orthogonal projection of `a` onto the line `z`)
```

of the tautological line `L`, and taking `a = e₀, …, e_{d-1}` — the first `d` standard
basis vectors — gives a section of `L^{⊕d}` whose zero set is

```text
{ z : z e₀ = ⋯ = z e_{d-1} = 0 } = { the line orthogonal to span(e₀,…,e_{d-1}) }
                                 = { e_d e_dᴴ },
```

a single point.  For a product `Y = ∏_j ℂP^{d_j}` and `H = ⊕_j L_j^{⊕d_j}` one takes
the product of these sections, whose zero set is the product of the singletons — again
one point.  So the manuscript's `±1` is an honest count of one zero, with no
characteristic class anywhere.

The zero is nondegenerate: `LIXObstructionTautChart.lean` computes the section in the
affine chart around `e_d e_dᴴ` and finds it to be, up to a positive scalar, the
componentwise conjugation `w ↦ (w̄₁, …, w̄_d)`.

## Main results

* `constSection` — the section of `L` cut out by a constant vector, and its continuity.
* `constSection_eq_zero_iff_inner_eq_zero` — it vanishes at `z` iff `a ⊥ z`.
* `constSections_eq_zero_iff` — the `d`-tuple vanishes at `z` iff `z = e_d e_dᴴ`.
* `constSections_zero_locus` — the zero set is the singleton `{cpBasepoint d}`.
-/

namespace GroupApproximation
namespace STW59

open Matrix

/-! ### The section cut out by a constant vector -/

/-- The section of the tautological line `L → ℂP^d` cut out by a constant vector `a`:
its value at a line `z` (a rank-one projection) is the orthogonal projection `z a` of
`a` onto that line. -/
def constSection (d : ℕ) (a : Fin (d + 1) → ℂ) (z : CP d) : Fin (d + 1) → ℂ :=
  (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) *ᵥ a

theorem constSection_apply (d : ℕ) (a : Fin (d + 1) → ℂ) (z : CP d) (i : Fin (d + 1)) :
    constSection d a z i = ∑ j, (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) i j * a j :=
  rfl

/-- The section really is a section of the tautological line: its value at `z` lies in
the range of the projection `z`. -/
theorem constSection_mem_line (d : ℕ) (a : Fin (d + 1) → ℂ) (z : CP d) :
    (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) *ᵥ constSection d a z = constSection d a z := by
  have h : (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) *ᵥ constSection d a z
      = ((z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
          * (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)) *ᵥ a :=
    Matrix.mulVec_mulVec _ _ _
  rw [h, (isProj_of_mem_cpSet z.2).2]
  rfl

theorem continuous_constSection (d : ℕ) (a : Fin (d + 1) → ℂ) :
    Continuous (constSection d a) := by
  refine continuous_pi fun i => ?_
  have h : (fun z : CP d => constSection d a z i)
      = fun z : CP d => ∑ j, (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) i j * a j := rfl
  rw [h]
  exact continuous_finset_sum _ fun j _ =>
    ((continuous_subtype_val.matrix_elem i j)).mul continuous_const

/-! ### Values on a rank-one projection -/

/-- On `z = x xᴴ` the section is `⟨x, a⟩ · x`: a scalar multiple of `x`, as it must be. -/
theorem rankOne_mulVec {m : ℕ} (x a : Fin m → ℂ) (i : Fin m) :
    (rankOne x *ᵥ a) i = x i * ∑ j, star (x j) * a j := by
  have h : (rankOne x *ᵥ a) i = ∑ j, rankOne x i j * a j := rfl
  rw [h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [rankOne_apply]
  ring

theorem exists_ne_zero_of_mem_unitVectors {m : ℕ} {x : Fin m → ℂ}
    (hx : x ∈ unitVectors m) : ∃ i, x i ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  rw [mem_unitVectors_iff] at hx
  simp only [hcon, norm_zero] at hx
  simp at hx

/-- **The section cut out by `a` vanishes at the line `z = x xᴴ` exactly when `a` is
orthogonal to that line.** -/
theorem constSection_rankOne_eq_zero_iff {m : ℕ} {x : Fin m → ℂ}
    (hx : x ∈ unitVectors m) (a : Fin m → ℂ) :
    rankOne x *ᵥ a = 0 ↔ ∑ j, star (x j) * a j = 0 := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := exists_ne_zero_of_mem_unitVectors hx
    have hi' := congrFun h i
    rw [rankOne_mulVec] at hi'
    simp only [Pi.zero_apply] at hi'
    exact (mul_eq_zero.mp hi').resolve_left hi
  · intro h
    funext i
    simp [rankOne_mulVec, h]

/-- The version stated on `ℂP^d`. -/
theorem constSection_eq_zero_iff_inner_eq_zero {d : ℕ} {x : Fin (d + 1) → ℂ}
    (hx : x ∈ unitVectors (d + 1)) (a : Fin (d + 1) → ℂ) :
    constSection d a ⟨rankOne x, rankOne_mem_cpSet hx⟩ = 0 ↔ ∑ j, star (x j) * a j = 0 :=
  constSection_rankOne_eq_zero_iff hx a

/-! ### The standard basis vectors, and the single common zero -/

theorem single_mem_unitVectors {m : ℕ} (k : Fin m) :
    (Pi.single k (1 : ℂ)) ∈ unitVectors m := by
  classical
  rw [mem_unitVectors_iff, Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- Evaluating the section at a standard basis vector reads off a column of `z`. -/
theorem constSection_single_apply (d : ℕ) (k : Fin (d + 1)) (z : CP d) (i : Fin (d + 1)) :
    constSection d (Pi.single k 1) z i
      = (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) i k := by
  have h : constSection d (Pi.single k 1) z
      = (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) *ᵥ Pi.single k 1 := rfl
  rw [h, Matrix.mulVec_single_one]
  rfl

/-- The line spanned by the **last** standard basis vector: the unique common zero of the
sections cut out by the first `d` standard basis vectors. -/
def cpBasepoint (d : ℕ) : CP d :=
  ⟨rankOne (Pi.single (Fin.last d) 1), rankOne_mem_cpSet (single_mem_unitVectors _)⟩

@[simp]
theorem cpBasepoint_coe (d : ℕ) :
    (cpBasepoint d : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
      = rankOne (Pi.single (Fin.last d) 1) := rfl

/-- **The explicit `d`-tuple of sections of `L` over `ℂP^d` vanishes at exactly one
point.**

The sections are the ones cut out by the first `d` standard basis vectors of `ℂ^{d+1}`;
their common zero set is the single line orthogonal to all of them, namely the one
spanned by the last basis vector.  This replaces the manuscript's
`|⟨c_m(H), [Y]⟩| = 1` at (2.1) by an explicit count of one zero. -/
theorem constSections_eq_zero_iff (d : ℕ) (z : CP d) :
    (∀ k : Fin d, constSection d (Pi.single k.castSucc 1) z = 0)
      ↔ (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
          = rankOne (Pi.single (Fin.last d) 1) := by
  classical
  obtain ⟨x, hx, hzx⟩ := taut_eq_rankOne d z
  rw [taut_apply] at hzx
  constructor
  · intro h
    -- every coordinate but the last vanishes
    have hk : ∀ k : Fin d, x k.castSucc = 0 := by
      intro k
      obtain ⟨i, hi⟩ := exists_ne_zero_of_mem_unitVectors hx
      have hval := congrFun (h k) i
      rw [constSection_single_apply, hzx, rankOne_apply] at hval
      simp only [Pi.zero_apply] at hval
      have := (mul_eq_zero.mp hval).resolve_left hi
      simpa using this
    have hzero : ∀ b : Fin (d + 1), b ≠ Fin.last d → x b = 0 := by
      intro b
      induction b using Fin.lastCases with
      | last => intro hb; exact absurd rfl hb
      | cast k => intro _; exact hk k
    -- so the last coordinate is a unit scalar
    have hnorm : ‖x (Fin.last d)‖ ^ 2 = 1 := by
      have hs := hx
      rw [mem_unitVectors_iff, Finset.sum_eq_single (Fin.last d)] at hs
      · exact hs
      · intro b _ hb
        rw [hzero b hb]
        simp
      · intro hb
        exact absurd (Finset.mem_univ _) hb
    have hlast : x (Fin.last d) * star (x (Fin.last d)) = 1 := by
      rw [mul_star_self_eq_normSq, hnorm]
      norm_num
    rw [hzx]
    ext i j
    rw [rankOne_apply, rankOne_apply]
    by_cases hj : j = Fin.last d
    · subst hj
      by_cases hi : i = Fin.last d
      · subst hi
        rw [hlast]
        simp [Pi.single_apply]
      · rw [hzero i hi]
        simp [Pi.single_apply, hi]
    · rw [hzero j hj]
      simp [Pi.single_apply, hj]
  · intro hz k
    funext i
    rw [constSection_single_apply, hz, rankOne_apply]
    have hne : (k.castSucc : Fin (d + 1)) ≠ Fin.last d := (Fin.castSucc_lt_last k).ne
    simp [Pi.single_apply, hne]

/-- The zero set of the explicit `d`-tuple of sections is a single point. -/
theorem constSections_zero_locus (d : ℕ) :
    {z : CP d | ∀ k : Fin d, constSection d (Pi.single k.castSucc 1) z = 0}
      = {cpBasepoint d} := by
  ext z
  rw [Set.mem_setOf_eq, Set.mem_singleton_iff, constSections_eq_zero_iff]
  exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩

end STW59
end GroupApproximation
