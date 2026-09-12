import GroupApproximation.CharClass.LIXShapeGeneric
import GroupApproximation.CharClass.LemmaTwoTopClass
import GroupApproximation.CharClass.LemmaTwoParity

/-!
# The bundle rank and the top degree at sphere rank `n`

Lane `sp-tower` of the STW Problem LIX strengthening programme
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`, §1.1).

`sp-design`'s lemma lists for `sp-oddside-n` and `sp-evenside-n` both end at the same three
declarations, with the note that **one lane must own each**: `LemmaTwoTopClass.lixRank`,
`LIXSectionLocalHomeo.lixTopDegree` and `LemmaTwoParity.trace_Vmat`.  They are the numeral
dictionary of the whole Step C and Step D chain, they are the only place the sphere rank
enters either side arithmetically, and they belong to the `Gen` shape layer.  This file is
that ownership.

## Two ranks, and they are not the same number

`n` is the **sphere rank**: the base is `S^{2n+1} ⊂ ℂ^{n+1}` and the trivial block of
`V = 𝟏^{n+1} ⊕ H` has `n+1` columns.  `r = lixRank n dd` is the **bundle rank**, the
pointwise rank of `V` and of the mapping torus, which `trace_Vmat` computes:

```text
   lixRank n dd      = (∑ⱼ dⱼ) + (n+1)          was  (∑ⱼ dⱼ) + 3
   lixTopDegree n dd = 2·(∑ⱼ dⱼ) + 2·(n+1)      was  2·(∑ⱼ dⱼ) + 6
```

Nothing else in either chain mentions a numeral, so redefining these two is a parameter
change rather than new mathematics.

## The spelling is load-bearing

`(∑ⱼ dⱼ) + (n+1)` and **never** `(n+1) + (∑ⱼ dⱼ)`.  `Nat.add` recurses on its second
argument, so only the first is definitionally the landed `+ 3` when the sum is a variable,
and only the first keeps `§3`'s bridges `rfl`.  `sp-evenside-n` adopted the same convention
independently for the top index, which is the agreement this file records.

For the top degree, `2·(n+1)` and `2·n+2` are interchangeable: `Nat.mul` recurses on its
second argument too, so `Nat.mul_succ` makes them the same term.  `sp-oddside-n` may write
either.

## `H` does not see the sphere rank

`trace_Hmat` carries no `n` at all.  It is stated over the point of `Y` alone, matching
`CharClass/LIXShapeGeneric.lean`'s re-indexing of `Hmat`, and it is the reason `trace_Vmat`
is one rewrite: the whole rank dependence of the trace is `Matrix.trace (1 : Matrix (Fin
(n+1)) (Fin (n+1)) ℂ)`.

## Main results

* `Gen.lixRank`, `Gen.lixTopDegree` — the two definitions, owned here.
* `Gen.lixTopDegree_eq_two_mul_lixRank` — `2r`, unchanged in form.
* `Gen.trace_Hmat`, `Gen.trace_Vmat` — **the rank of `V` is `r`**, at every sphere rank.
* `Gen.le_lixRank`, `Gen.one_le_lixRank`, `Gen.two_le_two_mul_lixRank` — the positivity
  the Step C chain consumes.
* `§3` — the rank-two bridges, both `rfl`.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open GroupApproximation.STW59
open GroupApproximation.AlgTop.CPn

set_option linter.unusedSectionVars false

namespace Gen

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. The trace of `V` -/

/-- The trace of `H`, over the point of `Y` alone.  Each block of `H` is a rank-one
projection, so the trace counts the blocks, and there are `∑ⱼ dⱼ` of them.  No sphere rank
appears. -/
theorem trace_Hmat (y : baseY dd) : Matrix.trace (Hmat y) = ((∑ j, dd j : ℕ) : ℂ) := by
  rw [Hmat, Matrix.trace_blockDiagonal']
  have hone : ∀ b : HBlk dd,
      Matrix.trace ((y b.1 : CP (dd b.1)) :
        Matrix (Fin (dd b.1 + 1)) (Fin (dd b.1 + 1)) ℂ) = 1 := fun b => trace_coe (y b.1)
  rw [Finset.sum_congr rfl fun b (_ : b ∈ Finset.univ) => hone b]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  rw [Finset.card_univ, Fintype.card_sigma]
  simp

/-- **The rank of `V = 𝟏^{n+1} ⊕ H` is `(∑ⱼ dⱼ) + (n+1)`**, at every sphere rank.  This is
the number `lixRank` names and the only arithmetic the rank contributes to either side of
Lemma 2. -/
theorem trace_Vmat (n : ℕ) (m : baseM n dd) :
    Matrix.trace (Vmat n m) = (((∑ j, dd j : ℕ) + (n + 1) : ℕ) : ℂ) := by
  rw [Vmat, trace_fromBlocks_gen, trace_Hmat, Matrix.trace_one, Fintype.card_fin]
  push_cast
  ring

/-! ## 2. The two numerals -/

/-- The bundle rank `r = (∑ⱼ dⱼ) + (n+1)` of the mapping torus, which `trace_Vmat`
computes.  Written with the sum first: `Nat.add` recurses on its second argument, so this
and not `(n+1) + (∑ⱼ dⱼ)` is definitionally the mod-two programme's `+ 3`. -/
def lixRank (n : ℕ) (dd : Fin ℓ → ℕ) : ℕ := (∑ j, dd j) + (n + 1)

/-- `dim N = 1 + (2n+1) + 2∑ⱼ dⱼ`, the top degree of `H^*(N; F₂)`. -/
def lixTopDegree (n : ℕ) (dd : Fin ℓ → ℕ) : ℕ := 2 * (∑ j, dd j) + 2 * (n + 1)

theorem lixTopDegree_eq_two_mul_lixRank (n : ℕ) (dd : Fin ℓ → ℕ) :
    lixTopDegree n dd = 2 * lixRank n dd :=
  (mul_add 2 (∑ j, dd j : ℕ) (n + 1)).symm

theorem trace_Vmat_eq_lixRank (n : ℕ) (m : baseM n dd) :
    Matrix.trace (Vmat n m) = ((lixRank n dd : ℕ) : ℂ) := trace_Vmat n m

/-! ## 3. Positivity -/

theorem le_lixRank (n : ℕ) (dd : Fin ℓ → ℕ) : n + 1 ≤ lixRank n dd := by
  rw [lixRank]
  exact Nat.le_add_left _ _

theorem one_le_lixRank (n : ℕ) (dd : Fin ℓ → ℕ) : 1 ≤ lixRank n dd :=
  le_trans (Nat.le_add_left 1 n) (le_lixRank n dd)

theorem lixRank_pos (n : ℕ) (dd : Fin ℓ → ℕ) : 0 < lixRank n dd := one_le_lixRank n dd

theorem two_le_two_mul_lixRank (n : ℕ) (dd : Fin ℓ → ℕ) : 2 ≤ 2 * lixRank n dd := by
  have h := one_le_lixRank n dd
  omega

theorem two_le_lixTopDegree (n : ℕ) (dd : Fin ℓ → ℕ) : 2 ≤ lixTopDegree n dd := by
  rw [lixTopDegree_eq_two_mul_lixRank]
  exact two_le_two_mul_lixRank n dd

end Gen

/-! ## 4. The rank-two bridges

Both are `rfl`: `n + 1` at `n = 2` is the literal `3` and `2 * (n + 1)` is the literal `6`,
so the landed definitions **are** their own `n = 2` instances and every consumer of
`lixRank` or `lixTopDegree` in the mod-two chain is untouched. -/

variable {ℓ : ℕ}

theorem lixRank_eq_gen (dd : Fin ℓ → ℕ) : lixRank dd = Gen.lixRank 2 dd := rfl

theorem lixTopDegree_eq_gen (dd : Fin ℓ → ℕ) : lixTopDegree dd = Gen.lixTopDegree 2 dd := rfl

end GroupApproximation.CharClass
