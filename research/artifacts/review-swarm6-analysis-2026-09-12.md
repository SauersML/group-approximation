# Review of swarm 6: analysis, soficity and C*-algebra claims landed after 17:00

Lane `swarm6-reviewer-analysis`, 2026-09-12 (swarm 7). This is an adversarial review of
the ESTABLISHED claims that swarm 6 landed after about 17:00 in analysis, soficity
and C*-algebras. The tip read was b04b42d61.

Verdicts:
- **PASS:** correct as stated.
- **GAP:** a missing step or an overstatement that this review does not fill.
- **FAIL:** false, or the proof does not work.

A citation is marked "source re-read" only when this lane read the statement from
the paper itself.

**Skipped, because a verdict already exists** (in
`research/artifacts/review-swarm4-2026-09-12.md` unless noted):
- §35.1 `leavitt-pair-vertex-rounding-is-nonhyperlinearity`;
- §35.2 `kazhdan-rank-rounding-fails-over-every-field`;
- §38.2 `kazhdan-kernel-isotypic-sectors-extend-within-kernel-closure`;
- §38.3 `bounded-multiplicity-kazhdan-sectors-miss-leavitt-cover-defect`;
- §38.4, the UCT and Cartan claims of 2558a1877;
- §29.5 `o2-zp-cartan-fixing-iff-rokhlin-uct-ascent`;
- §34.1 `gardella-rokhlin-actions-preserve-uct`;
- §34.4, the Sp(2,1) claims of c48a38ab6;
- §21, Thompson's V and the Cuntz groupoid;
- §31, the flexible HS claims;
- §12 of `research/artifacts/review-swarm5-2026-09-12.md`, the stw01 claim.

This lane's own line-by-line reading of the first four agreed with those verdicts
before they landed.

---

## 1. `ultrapower-comparison-with-rank-density-divides-projections`: PASS

Route: `ultrapower-comparison-rank-density-division-proof`, artifact
`research/artifacts/tw-invisible-gamma-support-gap-2026-09-12.md` §3. No
literature is imported. Every step was re-derived here.

- **Step 1 (represent).**
  - A projection `p ∈ M_k(A^U)` lifts to positive contractions `p_m`.
  - By Cauchy–Schwarz, `sup_τ τ(p_m − p_m²)` is bounded by a multiple of the uniform
    2-norm of `p_m − p_m²`, and that norm tends to 0.
  - Correct.
- **Step 2 (select).**
  - `τ ↦ τ(p_m)/n` is continuous and affine with values in `[0, k/n] ⊆ [0, k]`, so
    RD_b applies.
  - For a positive contraction, `0 ≤ b − b² ≤ 1` gives `τ((b − b²)²) ≤ τ(b − b²)`. So
    `(b_m)` has vanishing uniform 2-norm defect, and `e'` is a projection.
  - For a limit trace `σ = lim_U τ_m`, `σ(e') = lim_U τ_m(p_m)/n = σ(p)/n`.
  - Correct.
- **Step 3 (peel).** For `j ≤ n − 2`, the projection `p − (e_1 + … + e_j)` has
  profile `(n − j)σ(e') ≥ σ(e')` on every limit trace. So PC gives a subprojection
  `e_(j+1) ~ e'`. Correct.
- **Step 4 (remainder).**
  - `r = p − Σ_(i<n) e_i` has profile `σ(e')`. PC gives `w` with `w*w = e'` and
    `ww* ≤ r`.
  - Suppose a positive `x ∈ M_k(A^U)` vanishes on every limit trace but is nonzero.
    A positive lift has `lim_U sup_τ τ(x_m) > 0`, and a maximizing trace at each
    index defines a limit trace that is positive on `x`. So `x = 0`.
  - Hence `r = ww*` and `r ~ e'`. Correct.
- **Step 5 (assemble).**
  - Put `w_i* w_i = e'` and `w_i w_i* = e_i` for `i ≤ n`, with `e_n = r`.
  - `E_ij = w_i w_j*` are matrix units with `Σ E_ii = p`, giving a unital
    `M_n ⊆ p M_k(A^U) p`.
  - Correct.
- **Hidden hypotheses.**
  - Simplicity, separability and non-elementarity are stated but never used.
  - PC is assumed only for limit traces, and every trace the proof uses is a limit
    trace. No tracial state of `A^U` beyond the limit traces is needed.
- **Consistency.** This is the corner form of §4.1 of
  `research/artifacts/toms-winter-tracial-ultrapower-comparison-2026-09-12.md`,
  which passed in `research/artifacts/review-toms-winter-ultrapower-comparison-2026-09-12.md`.
  PC replaces strict comparison, and the matrix size is fixed.
