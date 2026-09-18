---
rg: 2
id: houghton-groups-have-polynomial-dehn-function
kind: claim
title: "For every n >= 3, Houghton's group H_n has a polynomially bounded Dehn function"
---

For every `n >= 3` there is an integer `d` with `δ_(H_n)(x) ≼ x^d`, for any
finite presentation of `H_n`.

S. R. Lee (arXiv:1212.0257, Theorem D) proves `δ_(H_n)(x) ≼ e^x`; this claim
asks for a polynomial improvement.

## Attempts

- 2026-09-13 (z1-24-houghton): reduction in progress. The translation part
  `Z^(n-1)` costs `O(x^2)`. Every null-homotopic word of length `x` becomes,
  after `O(x^2)` relator applications, a product of at most `O(x^2)`
  conjugates of the basic transposition `α` by words of length `<= x`. The
  symmetric-group word problem for a product of `M` transpositions on `m`
  points is solved with `O(M m)` applications of the transposition relations
  `τ^2 = 1`, `τ σ = σ τ^σ` (carry-and-merge elimination of one point at a
  time). So a polynomial bound follows once every such transposition relation
  between conjugates of `α` by words of length `O(x)` has polynomial area in
  `H_n`. That is the open crux.
- 2026-09-18 (swarm-0917-w8-w8-z-break, host-geometry: five-ray pour splitting).
  **Partial; the node stays open, and n = 3, 4 are the missing holes.**
  - Proved `houghton-groups-with-five-or-more-rays-have-polynomial-dehn`
    (`δ ≼ x^(6+log_2 5)` for `n >= 5`), in
    `research/artifacts/zp-houghton-five-rays-2026-09-17.md` (unreviewed).
  - The six-ray note uses two auxiliary rays only to commute a correction pour
    past a middle pour letterwise. Instead, route the middle pour via the single
    auxiliary ray `e`. Then commute the correction pour past each half
    `λ_ae^(m_2)`, `λ_eb^(m_2)` separately, changing its route from `b` to `a`
    between the halves.
  - This gives `W(m_1+m_2) <= 3W(m_1) + 2W(m_2) + 4m_1m_2 + 4m_1`, hence
    `W ≼ m^(log_2 5)`. The derivation was machine-checked
    (`experiments/houghton-five-rays-2026-09-17/verify_splitting.py`).
  - Added route `houghton-polynomial-dehn-by-ray-count`, splitting by ray count.
    Its OPEN prerequisites are `houghton-group-h4-has-polynomial-dehn-function`
    and `houghton-group-h3-has-polynomial-dehn-function`.
  - With four rays, every half-pour of the middle pour moves a ray of the
    correction pour, so the trick has no analogue there.
