import GroupApproximation.CharClass.LIXShapeGeneric
import GroupApproximation.Analysis.LIXLemmaTwoProp

/-!
# The single topological input of the LIX endpoint, generic in the rank

Lane `sp-tower` of the STW Problem LIX strengthening programme
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`, §1.1).

`Analysis/LIXLemmaTwoProp.lean` names the one proposition the C⋆-side takes on faith, at
rank two.  This file names it at rank `n`, over the rank-generic shape layer of
`CharClass/LIXShapeGeneric.lean`, and proves that the rank-two `Prop` is its own `n = 2`
instance (`§3`).

## The section is the parameter, and that is where `k` will enter

`LemmaTwoHolds` compares two complements inside one `V = 𝟏^{n+1} ⊕ H`: the complement of
the tautological section `s (x, y) = x` and the complement of the constant section
`e = e_last`.  Nothing in the statement uses anything about `s` beyond its being a
**continuous unit section of the trivial block**, so this file states the seam for an
arbitrary such section (`LemmaTwoFor`) and defines `LemmaTwoHolds n` as the instance at
`bVec n`.

That is deliberate.  The renormalised-generator programme replaces the tautological
section by a section of winding `k`; when `sp-powers`' `exists_homotopy_pow_comp_normGen`
lands, the `k`-indexed seam is `LemmaTwoFor n (lixDD n j) b_k` with no change to any
statement here and no change to the reduction.  Naming the section rather than the
winding is what keeps this file independent of how the degree-`k` section is built.

## The dimensions

`lixDD n j` is `(d_0, …, d_{j-1})` at stage `j` of the rank-`n` tower, `d_i = r_i = n·2^i`
(`STW59.Gen.stageRank`).  `even_lixDD` needs `Even n`, which is the rank-`n` form of what
Step D consumes: `γ(V) = ∏_i (1 + h_i)^{d_i}` is supported in degrees `4k` exactly because
each `d_i` is even, and at rank `n` that is a hypothesis on `n` rather than a theorem.
`dvd_lixDD` is the form the mod-`p` argument wants.

## Main results

* `Gen.lixDD`, `Gen.even_lixDD`, `Gen.lixDD_pos`, `Gen.dvd_lixDD` — the dimensions.
* `Gen.LemmaTwoFor` — the seam, for an arbitrary unit section.
* `Gen.LemmaTwoHolds` — the seam at the tautological section, at every stage.
* `§3` — `LemmaTwoHolds ↔ Gen.LemmaTwoHolds 2`, by `Iff.rfl`.
-/

namespace GroupApproximation
namespace LIX

namespace Gen

variable {ℓ : ℕ}

/-! ## 1. The dimensions at rank `n` -/

/-- The `ℂP` dimensions carried by stage `j` of the rank-`n` LIX tower: `d_i = n·2^i`
for `i < j`.  At `n = 2` this is `LIX.lixDD`. -/
def lixDD (n j : ℕ) : Fin j → ℕ := fun i => STW59.Gen.stageRank n (i : ℕ)

@[simp] theorem lixDD_apply (n j : ℕ) (i : Fin j) : lixDD n j i = 2 ^ (i : ℕ) * n := rfl

/-- Every dimension is even as soon as the rank is, which is the hypothesis Step D runs
on.  At rank two it is automatic; at rank `n` it is a condition on `n`. -/
theorem even_lixDD {n : ℕ} (hn : Even n) (j : ℕ) (i : Fin j) : Even (lixDD n j i) := by
  rw [lixDD_apply]
  exact hn.mul_left _

/-- Every dimension is positive. -/
theorem lixDD_pos (n j : ℕ) [NeZero n] (i : Fin j) : 0 < lixDD n j i :=
  STW59.Gen.stageRank_pos n (i : ℕ)

/-- A divisor of the rank divides every dimension.  This is the shape the mod-`p`
argument consumes, and it is why the rank carries the prime rather than the stage. -/
theorem dvd_lixDD {p n : ℕ} (h : p ∣ n) (j : ℕ) (i : Fin j) : p ∣ lixDD n j i :=
  STW59.Gen.dvd_stageRank h (i : ℕ)

/-! ## 2. The seam at rank `n` -/

/-- The complement, inside `V = 𝟏^{n+1} ⊕ H`, of an arbitrary continuous unit section `b`
of the trivial block.  At `b = bVec n` this is `CharClass.Gen.FHmat n`, on the nose. -/
def FHmatOf (n : ℕ) {dd : Fin ℓ → ℕ}
    (b : CharClass.Gen.baseM n dd → Fin (n + 1) → ℂ) (m : CharClass.Gen.baseM n dd) :
    Matrix (CharClass.Gen.VIdx n dd) (CharClass.Gen.VIdx n dd) ℂ :=
  CharClass.Gen.Vmat n m - Matrix.fromBlocks (STW59.rankOneProj (b m)) 0 0 0

theorem FHmatOf_bVec (n : ℕ) {dd : Fin ℓ → ℕ} (m : CharClass.Gen.baseM n dd) :
    FHmatOf n (CharClass.Gen.bVec n) m = CharClass.Gen.FHmat n m := rfl

/-- **Lemma 2 of the manuscript for the unit section `b`**, at rank `n` over the
coefficient datum `dd`: the complement of `b` and the complement of the constant section
`e_last` are not Murray--von Neumann equivalent as continuous fields over
`M = S^{2n+1} × ∏ⱼ ℂP^{dⱼ}`.

Both complements have the same pointwise rank, so this is not refutable from the trace.
The winding index `k` of the renormalised-generator programme enters here and only here,
as which section `b` is. -/
def LemmaTwoFor (n : ℕ) (dd : Fin ℓ → ℕ)
    (b : CharClass.Gen.baseM n dd → Fin (n + 1) → ℂ) : Prop :=
  ¬ CharClass.ContinuousMvNEquiv (FHmatOf n b) (CharClass.Gen.EHmat n)

theorem lemmaTwoFor_bVec_iff (n : ℕ) (dd : Fin ℓ → ℕ) :
    LemmaTwoFor n dd (CharClass.Gen.bVec n)
      ↔ ¬ CharClass.ContinuousMvNEquiv
          (CharClass.Gen.FHmat (n := n) (dd := dd)) (CharClass.Gen.EHmat n) := Iff.rfl

/-- **Lemma 2 at every stage of the rank-`n` tower**, at the tautological section.  This
is the rank-`n` form of `LIX.LemmaTwoHolds`, and the only statement the C⋆-side takes on
faith at any rank. -/
def LemmaTwoHolds (n : ℕ) : Prop :=
  ∀ j : ℕ, LemmaTwoFor n (lixDD n j) (CharClass.Gen.bVec n)

/-- The stage-`j` instance, which is the form a stage-level argument consumes. -/
theorem LemmaTwoHolds.at_stage {n : ℕ} (h : LemmaTwoHolds n) (j : ℕ) :
    ¬ CharClass.ContinuousMvNEquiv
        (CharClass.Gen.FHmat (n := n) (dd := lixDD n j)) (CharClass.Gen.EHmat n) :=
  (lemmaTwoFor_bVec_iff n (lixDD n j)).mp (h j)

end Gen

/-! ## 3. The rank-two bridge

The rank-two seam is its own `n = 2` instance, definitionally.  `2 ^ i * n` at `n = 2` is
the mod-two programme's `2 ^ (i + 1)` — `Nat.pow` recurses on the exponent — so `lixDD` is
a `rfl`, and with `CharClass/LIXShapeGeneric.lean`'s bridges the whole `Prop` is an
`Iff.rfl`.  Nothing that consumes `LemmaTwoHolds` has to change for the generic seam to
exist. -/

theorem lixDD_eq_gen (j : ℕ) : lixDD j = Gen.lixDD 2 j := rfl

theorem lemmaTwoHolds_iff_gen : LemmaTwoHolds ↔ Gen.LemmaTwoHolds 2 := Iff.rfl

end LIX
end GroupApproximation
