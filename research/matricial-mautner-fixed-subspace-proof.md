---
rg: 2
id: matricial-mautner-fixed-subspace-proof
kind: route
title: Stable finiteness of the corona forces the two Kazhdan projections equal
target: matricial-mautner-fixed-subspace
requires: []
artifacts:
  - research/artifacts/multi-mover-hnn-dossier-2026-08-15.md
---

## Why sufficient

Three steps, none of them analytic.

**The corona is stably finite.**  If `v* v = 1` in `Q = prod M_{d_n} / sum
M_{d_n}`, lift to a bounded sequence `v_n` with `v_n* v_n -> 1` in operator
norm.  For large `n` the matrix `v_n` is invertible, and in `M_{d_n}` a
one-sided inverse is two-sided, so `v_n v_n* -> 1` and `v v* = 1`.  Matrix
amplifications of `Q` are again coronas of the same shape (block size `m`
times the dimensions), so every `M_m(Q)` is finite too.

**The two projections are comparable one way and equivalent the other.**
`H <= pi(Gamma)` gives `p_Gamma <= p_H`: a Kazhdan projection is the image of
the corresponding projection in `C*max`, and in every representation the
`Gamma`-fixed part sits inside the `H`-fixed part, so `p_Gamma p_H =
p_Gamma`.  Separately `H` is the `t`-conjugate of `pi(Gamma)`, so its Kazhdan
projection is the `t`-conjugate of `p_Gamma`; conjugation by a unitary is a
Murray--von Neumann equivalence, so `p_H ~ p_Gamma`.

**Finiteness closes it.**  A projection `q <= p` with `q ~ p` forces `q = p`
in a finite algebra, applied here with `q = p_Gamma`, `p = p_H`.  Hence
`p_H = p_Gamma`.

## What this is and is not

It is the corona-level phrasing of the reversal already carried at the finite
stages by the equal-rank argument (dossier Lemma 33.12: two equal-rank
projections with `||(1-Q)P||` small have `||(1-P)Q||` equally small).  Finite
equal rank and stable finiteness are the same resource, read at two levels;
recording both is deliberate, because the compression proof in this
repository uses the stagewise form and the circulated source uses this one.

It is *not* a statement about almost representations: `pi` here is an honest
homomorphism into the corona, and the conclusion is an exact projection
identity.  The step that needs the analytic machinery is producing a vector
fixed by the compressed copy and not by `Gamma` in the first place; this
lemma is what makes such a vector impossible.

## Provenance

The lemma is what the circulated action-form criterion uses as its final
contradiction (`research/artifacts/collapse-criterion-source-2026-08-16.md`,
section 4 step 11, reported as Lemma 2.1 / Corollary 2.2 there).  That
attribution is second-hand.  The proof above is independent and is checked
here, so nothing downstream depends on the reported anchors.
