---
rg: 2
id: rf-toeplitz-subshift-has-computable-language
kind: claim
title: The residually finite Toeplitz subshift built from a computable chain has decidable language
distinct_from:
  rf-toeplitz-subshifts-over-residually-finite-groups: that builds the subshift and proves minimality, freeness and residual finiteness; this adds that its language is decidable when the chain is computable with decidable membership.
artifacts:
  - research/artifacts/sk-wp-embedding-decidable-envelopes-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `Δ` be finitely generated, infinite, effectively residually finite with solvable
word problem, and let `(Δ_m)` be a computable chain for it with decidable membership. Let `X_Δ` be the Toeplitz
subshift built from that chain in `rf-toeplitz-subshifts-over-residually-finite-groups`. Then

```text
L(X_Δ) = { (W,p) : W a finite set of words on the generators, p a pattern on W occurring in X_Δ }
```

is decidable, and the array `x` itself is computable: `γ ↦ x(γ)` is an algorithm.

The decision uses two searches that halt because `∩_m C_m = ∅` for the hole cosets and `∩_m Δ_m = {e}`: one finds
the level at which a position leaves the hole, the other a level `M` at which the elements of `W` lie in distinct
`Δ_M`-cosets, so that at most one position of any translate of `W` is still undetermined and that position is free.

Route: `rf-toeplitz-subshift-has-computable-language-proof`.

**Review (sk-verify-4, 2026-09-13): PASS, two wording notes.** Values at the first level leaving the hole, distinct-coset level by normality, fixed determined positions and both letters at the hole position re-derived. Notes: identify words of `W` equal in `Δ` (via `WP(Δ)`) before searching for `M`; and make every choice of Theorem T the least admissible one in a computable enumeration. See `research/artifacts/sk-review-4-2026-09-13-part5.md` §4.
