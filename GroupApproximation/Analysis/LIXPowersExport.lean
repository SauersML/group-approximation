import GroupApproximation.Analysis.LIXPowersChain
import GroupApproximation.CharClass.LemmaTwoStatement

/-!
# The export, in `CharClass` vocabulary

`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.3, deliverable 3 of the powers lane.
`Analysis/LIXPowersChain.lean` proves the geometry; this file states it in the vocabulary
`CharClass` and `Analysis/LIXLemmaSixCor4.lean` speak.

## The bridge is an identity

`Powers.ClutchEquiv` and `CharClass.ContinuousMvNEquiv` are the *same* definition unfolded,

```text
∃ w, Continuous w ∧ (∀ m, wᴴ w = P m) ∧ (∀ m, w wᴴ = Q m)
```

so `clutchEquiv_iff_continuousMvNEquiv` is `Iff.rfl`.  This is the only reason this file
imports `CharClass`; the clutching layer itself does not, and must not.

## Why this file is index-generic, and where the rank is pinned

The lead asked for the `n = 2` export.  The export theorem below is stated for an arbitrary
index type because **the `n = 2` specialisation is not a renaming**: the clutching layer's
projection lives in `Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ` with `ι = Fin 2`, i.e. rank `4`, while the
manuscript's `FHmat` lives in `Matrix (VIdx dd) (VIdx dd) ℂ` with
`VIdx dd = Fin 3 ⊕ HIdx dd`, i.e. rank `3 + m`.  Identifying them needs

* `clutch u ≅ Fproj` -- the manuscript's "the projection clutched by `u` is `F`", and
* the stabilisation by `H` and the reindexing that goes with it,

and the reindexing is *determined by* that identification, so hard-coding index types now
would mean inventing it.  The rank therefore enters exactly once, in the caller's choice of
`P` and of the index type, and nowhere in the geometry.  When `sp-tower`'s `Gen` versions of
`VIdx`/`baseM`/`Vmat`/`sProj`/`eProj`/`FHmat` land, the general-`n` export is this same
theorem at a different instantiation -- a restatement, not a rework.

## The one undischarged input, stated plainly

**`clutch u ≅ Fproj` is not in the tree.**  A grep over `GroupApproximation/` shows
`clutchMat`, `coneMat` and `clutchOfChart` occurring only in `Analysis/LIXClutching.lean`
and in this lane's own files; no `CharClass` file mentions them, and the existing
Corollary-4 chain (`LIXLemmaSixField` → `LIXLemmaSixCompare` → `LIXLemmaSixCor4`) does not
use the clutching layer at all.  `LIXGeneratorUnitary`'s module docstring says why: the pair
of hemisphere sections whose seam discrepancy is `u` is exactly what is *not* constructed
there, and "the same pair also gives `clutch u ≅ F`".

So the hypothesis `hP` of `clutchEquiv_pow_of_clutch_eq`, and of the export below, is a live
input and not a formality.  It is nobody's deliverable in the current lane table.  This file
names it rather than assuming it.
-/

namespace GroupApproximation
namespace LIX
namespace Powers

open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

section Bridge

variable {X : Type*} [TopologicalSpace X] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The vocabulary bridge.**  The clutching layer's equivalence relation is literally the
`CharClass` one. -/
theorem clutchEquiv_iff_continuousMvNEquiv (P Q : X → Matrix ι ι ℂ) :
    ClutchEquiv P Q ↔ CharClass.ContinuousMvNEquiv P Q := Iff.rfl

theorem ClutchEquiv.toContinuousMvNEquiv {P Q : X → Matrix ι ι ℂ} (h : ClutchEquiv P Q) :
    CharClass.ContinuousMvNEquiv P Q := h

theorem continuousMvNEquiv_toClutchEquiv {P Q : X → Matrix ι ι ℂ}
    (h : CharClass.ContinuousMvNEquiv P Q) : ClutchEquiv P Q := h

end Bridge

section Export

variable {X : Type*} [TopologicalSpace X] {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {e₁ e₂ : E} {n : Type*} [Fintype n] [DecidableEq n]
  {t : X → ℝ} {ν : X → E} {U : E → Matrix n n ℂ}

/-- **The export.**  Given the identification of the projection clutched by the generator
with a field `P` -- the manuscript's `clutch u = F ⊕ H`, the one undischarged input -- the
projection clutched by `u^{k+1}` is `ContinuousMvNEquiv` to `P` read at `Σψ_k`.

This is what `sp-oddside` consumes.  Everything geometric is in
`Analysis/LIXPowersChain.lean`; the only content added here is the vocabulary. -/
theorem continuousMvNEquiv_pow_of_clutch_eq (hc : IsSuspensionChart t ν) (h₁ : ‖e₁‖ = 1)
    (h₂ : ‖e₂‖ = 1) (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ)) (hU : IsBallUnitary U) (k : ℕ)
    {Φ : X → X} (hΦt : ∀ x, t (Φ x) = t x)
    (hΦν : ∀ x, ν (Φ x) = joinPowNeg e₁ e₂ k (ν x))
    {P : X → Matrix (n ⊕ n) (n ⊕ n) ℂ}
    (hP : ∀ x, clutchMat (t x) (coneMat U (ν x)) = P x) :
    CharClass.ContinuousMvNEquiv
      (fun x => clutchMat (t x) (coneMat (fun y => (U y) ^ (k + 1)) (ν x)))
      (fun x => P (Φ x)) :=
  clutchEquiv_pow_of_clutch_eq hc h₁ h₂ h₁₂ hU k hΦt hΦν hP

/-- The same without the identification, i.e. against the clutched projection itself.  A
caller who has `Σψ_k` realised as a self-map `Φ` but not yet the identification with `F ⊕ H`
can use this one today. -/
theorem continuousMvNEquiv_pow_pullback_map (hc : IsSuspensionChart t ν) (h₁ : ‖e₁‖ = 1)
    (h₂ : ‖e₂‖ = 1) (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ)) (hU : IsBallUnitary U) (k : ℕ)
    {Φ : X → X} (hΦt : ∀ x, t (Φ x) = t x)
    (hΦν : ∀ x, ν (Φ x) = joinPowNeg e₁ e₂ k (ν x)) :
    CharClass.ContinuousMvNEquiv
      (fun x => clutchMat (t x) (coneMat (fun y => (U y) ^ (k + 1)) (ν x)))
      (fun x => clutchMat (t (Φ x)) (coneMat U (ν (Φ x)))) :=
  clutchEquiv_pow_pullback_map hc h₁ h₂ h₁₂ hU k hΦt hΦν

end Export

end

end Powers
end LIX
end GroupApproximation
