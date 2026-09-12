---
rg: 2
id: linton-rational-derived-series-theorem
kind: claim
title: Linton's theorem on the rational derived series of a one-relator group
distinct_from:
  one-relator-soficity-localizes-at-rational-derived-stage: that is this graph's soficity consequence, proved here from the theorem below plus Elek--Szabó; this is the imported group-theoretic input itself, which mentions no approximation property at all.
  linton-radical-abelianization-is-truncated-group-ring: that computes the radical's first homology using Lyndon's identity theorem; this supplies the word `r` and the integer `k` that computation consumes, and computes nothing.
  one-relator-fox-magnus-descent-to-derived-linton-radical: that uses the Linton data in a mod-`k` Magnus embedding and obtains a sofic quotient with kernel `R'`; this imports only the structural data from Linton and has no Fox or approximation content itself.
  residually-rationally-solvable-one-relator-sofic: that is a soficity theorem about a subclass; this is the structural characterization of that subclass, with no soficity content.
artifacts:
  - research/artifacts/one-relator-soficity-audit-2026-08-17.md
---

ESTABLISHED by citation.  Marco Linton, *Residually rationally solvable
one-relator groups*, arXiv:2407.09272v2.  Let `G = F/<<w>>` be a one-relator
group and let `G_Q^(i)` be its rational derived series, `G_Q^(ω)` the
intersection.

> **Theorem 1.1.**  There is a word `r ∈ F`, of length bounded above by that of
> `w`, and an integer `k >= 1` such that `w ∈ r^k[<<r>>,<<r>>]` and
> `G_Q^(ω+1) = G_Q^(ω) = <<r>>_G`.

> **Corollary 1.2**, item (2): `G` is residually rationally solvable if and only
> if `G_Q^(n)` is a free group for some integer `n >= 0`.  "In fact, a
> consequence of our proofs is that the integer `n` from (2) may be taken to be
> the length of the relator `w`."

Together with the corollary's other consequence that `G/G_Q^(ω) = F/<<r>>` is
residually rationally solvable, these are the **only** sentences of that paper
used anywhere in this graph.  They were read from arXiv on 2026-08-17 and are
transcribed in the artifact.

## Trust surface

This is a literature import and is marked as one, so that everything resting on
it is visibly conditional on a preprint rather than on anything proved or
formalized here.  The paper is a self-contained group-theoretic argument by a
named author in his own area, published work adjacent to it (*One-relator
hierarchies*, Duke Math. J. **174** (2025)) is refereed, and no operator-algebra,
MF or corona content is involved, so there is no priority interaction with the
manuscript.

Two things this node deliberately does **not** import.  First, the source
document that occasioned this region attributed to Linton a *two-case* finite
stage statement — free in the residually rationally solvable case, and an
extension of `G_Q^(ω)` by a free group otherwise.  Only the first case is
Corollary 1.2; the second is derived in
[[one-relator-soficity-localizes-at-rational-derived-stage]] from the sentences
above rather than quoted.  Second, nothing here asserts anything about
soficity, hyperlinearity or MF: Linton's paper contains no approximation
statement, and every approximation-theoretic consequence in this region is added
by this graph.
