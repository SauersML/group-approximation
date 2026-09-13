---
rg: 2
id: labbe-wang-shift-has-polynomial-pattern-complexity
kind: claim
title: Labbé's aperiodic Wang shift has polynomial pattern complexity, p(n) <= 50·4^9·n^16
distinct_from:
  labbe-shift-is-a-toral-rotation-coding: that gives zero topological entropy, which for Z^2 only bounds p(n) by e^{o(n^2)}; this gives a polynomial bound, which is what the rank-model route needs.
artifacts:
  - research/artifacts/un-labbe-ring-substitution-complexity-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `Ω_U` be Labbé's aperiodic Wang shift on 19 tiles, and let `p(n)` be the number of
distinct `n × n` patterns. For every `n >= 1`,

`p(n) <= 50 · 4^(8⌈log_2 n⌉+1) <= 50 · 4^9 · n^16`.

In particular `m ↦ m^2 p(2m+1)` grows polynomially, hence subexponentially.

**Proof idea** (route `labbe-wang-shift-has-polynomial-pattern-complexity-proof`, from
`labbe-substitution-is-primitive-and-recognizable`, which quotes arXiv:1802.03265 verbatim):
- Labbé's morphism `ω = αβγ` has letter images of shape at most `(2,2)`, is primitive (`M^7 > 0`), and sends some
  letter to a `(2,2)` word. So iterates double in both directions every 8 steps, and grow by at most a factor 2 per
  step.
- The language is self-similar. Every `n × n` pattern is covered by `ω^m` of one of the 50 legal `2×2` words, with
  `m = 8⌈log_2 n⌉`.

**Why it is wanted.** Together with
`subexponential-complexity-zd-subshift-rings-have-rank-models` it discharges, unconditionally and in
characteristic `p`, the rank-model assumption that
`rank-modelled-simple-algebra-with-non-lef-kazhdan-el-group` currently carries. The middle rung of
`kazhdan-elementary-approximation-type-mirrors-ring-type` would then rest only on non-matriciality, which is
`labbe-wang-shift-crossed-product-is-not-exactly-matricial`.

## Attempts

- **Expected from self-similarity: now verified.** The first version of this node expected polynomial complexity
  from primitive self-similarity without reading the source. un-labbe-ring read Labbé's TeX source on MSI. The
  count uses only primitivity, bounded letter images, a letter with a `(2,2)` image, and the cover step; the imported
  recognizability is not used.
- **Zero entropy alone is not enough.** Entropy for `Z^2` subshifts is `lim log p(n)/n^2`, so zero entropy
  only gives `p(n) = e^{o(n^2)}`, which permits `p(n) = e^{n}` and hence exponential growth of the ring. The
  downstream route needs genuinely subexponential `p`, not merely zero entropy. This is the one place where
  the `d = 1` and `d ≥ 2` cases differ: for `d = 1`, zero entropy is exactly subexponential complexity.
- **Sharp order `O(n^2)`: open here, not needed.** It needs either:
  - linear repetitivity, i.e. balanced growth of widths and heights of `ω^m(a)`, which the source does not state; or
  - a face count for the arrangement of translates of the polygonal Markov partition boundary
    (`labbe-shift-is-a-toral-rotation-coding`), using that every pattern occurs in a generic tiling by minimality.

**Review (un-verify-open, 2026-09-13, `research/artifacts/un-review-open-2026-09-13-part1.md` §3.2): PASS.** Letter-image shapes, the doubling every 8 steps, the cover step (Lemma 5 proof) and the bound 50·4^(m+1) ≤ 50·4^9·n^16 were re-derived. The rank-model consequence is correctly recorded in Attempts only; it also follows from `free-minimal-crossed-products-are-simple-with-rank-models`.
