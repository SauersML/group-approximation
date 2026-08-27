---
rg: 2
id: npa-critical-face-first-order-dimension-law
kind: claim
title: The critical-face first-order space has dimension two k plus three at every NPA level
artifacts:
  - research/artifacts/npa-critical-face-dimension-law-audit-2026-08-23.md
---

For every `k >= 2`,

```text
dim V_k = 2k + 3,
```

equivalently `dim ker Phi_k = 2k+3`, equivalently
`rank Phi_k = (5k^2 + 3k - 4)/2`.

The evidence is the computed sequence `7, 9, 11, 13` at `k = 2, 3, 4, 5`.  That
computation is the ingesting dossier's, performed inside the source's framework
and consistent with the range `k = 2..5` over which the source runs its own
structural checks; **the source is not known to print a dimension table, to state
this law, or to label it a conjecture.**  Three independent retrievals of
arXiv:2607.13762 found no occurrence of `2k+3`, no token `R2`, no phrase
"the matching upper bound is open" and no phrase "structural conjecture", and
its Section 9.1 came back as three open questions concerning overshoot
exponents, the convergence rate of `eps_k`, and structure off the critical line.
The companion arXiv:2607.13774 has none of it either.  Those retrievals are
model-rendered rather than a grep of the source, so the audit records the
question as strongly evidenced but not settled, and this region treats the law
as an unsourced conjecture on its own merits.

What makes it interesting is not the linear formula but the mechanism proposed
for it: each shell of `5k+1` new moment classes splits as `(5k-3)` forced
directions plus `4` exceptional ones, while exactly `2` inherited gauge freedoms
are consumed, so the nullity rises by `4 - 2 = 2` per level.  That decomposition,
if proved, is the publishable content; the dimension law is its corollary
through `npa-class-count-fixes-rank-nullity-dictionary`.

## Attempts

The only attack on record is the two-sided split: prove the upper bound by the
triangular-shell induction and take the lower bound from an explicit
construction.  Both halves are open, and the audit's finding is that the second
half has been carried in the literature-facing account by attribution rather
than by proof.

The upper half is one lemma short -- see
`npa-unseen-classes-are-free-at-level-k`, which is where the induction actually
stops.  The dossier author has since withdrawn the closure claim on exactly that
point.

Not yet tried, and cheap: build `Phi_k` and compute `dim ker Phi_k` directly at
`k = 6, 7`, beyond the source's verified range.  Every number quoted in support
of this claim sits inside `k <= 5`, and the supplied verifier checks the shell
combinatorics without ever computing a nullity, so two more data points would be
the first independent evidence the law has.
