# hl-lemma46 (lane report, 2026-09-13)

Scope: Hyde–Lodha Lemma 4.6 (tex 867–869, `\label{FPlem3}`), at the generality Proposition 4.7
consumes. The 09-13 final split (roster) runs through simple-group's interface
`HydeLodha/QTwoLemmaFourSixStatements` (232d6b12b):
- hl-lemma46: `LemmaFourSixDynamicsStatement`.
- simple-group: `lemmaFourSixCaseOne_of_dynamics` and the final closed endpoint.
- kh-ejz: the casing pair and conjugation into the unit frame.
- fff-quotient: |I| = 1.

## Landed
- `HydeLodha/QTwoLemmaFourSixDynamics` (de535e84c; probe 0913-021539-18816 PROBE GREEN, BUILT, bytes = origin/main; closed axioms propext, Classical.choice, Quot.sound; in wire-queue).
  - Endpoint: `theorem lemmaFourSixDynamics : LemmaFourSixDynamicsStatement`, with `#audit_closed_axioms`.
  - Helpers, with `#audit_axioms`:
    - `germRight_iterate_le`: mirror of `germLeft_iterate_ge`.
    - `disjoint_perIoo_of_le`: disjoint periodic intervals.
    - `exists_upsilon_gammaTwo_move`: `exists_move` made periodic through `perHom 4` and `upsilon_gammaTwo_eq_map`.
    - `exists_upsilon_qTwo_push`: one `t ∈ Υ_{Q₂}([e₁, e₂])` with `t d ≤ c`, the commutator of two moves.
    - `disjoint_pow_image`: the intervals `[c, d]·t^j` are pairwise disjoint.

## Construction (tex 874, 877–878, 888–889)
- **f.** `exists_upsilon_qTwo_germs` gives `f ∈ Υ_{Q₂}(I)` with the germ `t ↦ a + 6 (t − a)` at `a⁺` and the germ `t ↦ b + 6 (t − b)` at `b⁻`.
- **The intervals.** `λ = 6^{-L} ≤ min(ε, (b − a)/20)`. Then `J = [e₁, e₂] = [a + λ, b − λ]` and `[c, d] = [a + 2λ, b − 2λ]`. The germs give `f e₁ = a + 6λ ≥ c` and `f e₂ = b − 6λ ≤ d`.
- **Covering.** Take `k ∈ Υ^c_{Γ₂}(I)`, supported in `(a + δ, b − δ)`.
  - Choose `N` with `6^N min(δ, λ) ≥ 1`. The germ iterates put `f^N(a + δ') ≥ a + λ` and `f^N(b − δ') ≤ b − λ`.
  - One more step of `f` gives `a + 6λ` and `b − 6λ`.
  - So `f^{N+1} k f^{-(N+1)} ∈ Υ^c_{Γ₂}([c, d])` with margin `λ`.
- **The s_i.** `s_i = t^{i+1}`.
  - `K ∈ Υ_{Γ₂}(J)` moves a grid point `β ∈ (d, e₂)` below a grid point `α ∈ (e₁, c)`.
  - `H ∈ Υ_{Γ₂}([α, β])` moves `d` below `c`.
  - `t = ⁅H, K⁆ ∈ Q₂` is supported in `J`, and `t d = H d ≤ c`, because `K⁻¹ d ∈ [β, e₂]` is fixed by `H`.
  - `t^j d` decreases and `t^{j+1} d ≤ t^j c`, so the images `[c, d]·t^j` are pairwise disjoint and disjoint from `[c, d]`.

## Residual
- None in this lane: `LemmaFourSixDynamicsStatement` is closed.
- hW is one line from closed, in simple-group's `FinitelyPresentedInfiniteSimpleClosed`. It needs an import of `QTwoLemmaFourSixDynamics` and `finitelyPresentedInfiniteSimpleStatement_of_dynamics lemmaFourSixDynamics`. This was reported to the lead; the file is not this lane's.

## Census
- `metadata/nm-census-rows/hl-lemma46.tsv`: LINE:1679 `partial` (the FFF §2 "finitely presented infinite simple group", witness Q₂), carrying the dynamics.

## Next
- The Corollary 7.4 piece was superseded: cite-hull closed Hull Cor 7.4 (c6e0b6c33).
- Current item, from the lead after the 08:30 coordinator restart: help hull-select on W1.
  - Targets: the MultipleEdgeCut assembly (`multipleEdgeCutInput_of_pieces`) and the IsDiscRegion merge Prop.
  - Status: waiting for hull-select to name a sub-piece. Nothing is written yet.
  - Inputs the assembly composes:
    - kh-ejz's `MultipleEdgePocketRegionInput` (d00f94876);
    - the collar (`PocketCollarStatement` / kh-torsion's `GeodesicCollarStatement`);
    - go-lemma42's transport at j = 1, 3;
    - the zero-cell merge;
    - `OsinMultipleEdgeCut.ofPocketRegion` (45e7201da).
  - Observed blocker, passed to hull-select: `Estimating/OsinAppendixCutMerge.lean` (hull-respell) is red at line 103 (omega). Nothing landed on 09-13 touched it or its weight dependencies.
