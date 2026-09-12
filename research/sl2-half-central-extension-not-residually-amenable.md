---
rg: 2
id: sl2-half-central-extension-not-residually-amenable
kind: claim
title: The candidate central extension of SL_2(Z[1/2]) is not residually amenable
artifacts:
  - research/artifacts/two-paper-ingestion-2026-08-19.md
distinct_from:
  finite-central-extension-rf-iff-virtually-splits: that is the general criterion for residual finiteness of a finite central extension; this is the specific arithmetic conclusion for the Dogon-Vigdorovich candidate and goes further, to residual amenability.
  non-residually-finite-hyperbolic-group: that is the existence of a non-residually-finite hyperbolic group; this is a specific S-arithmetic amalgam, imports Deligne, Raghunathan and Margulis rather than constructing anything, and goes further, to residual amenability.
---

**Established by citation.**  Recorded by Dogon--Vigdorovich,
arXiv:2506.20843v2, in the prologue "A candidate for non-hyperlinearity",
immediately after their Corollary 1.3:

> By a theorem of Deligne and Raghunathan regarding central extensions of
> `S`-arithmetic groups, `Gamma~` is not residually finite.  Combined with
> Margulis' normal subgroup theorem, it is not residually amenable, making it
> an intriguing candidate for a non-hyperlinear group.

Here `Gamma~` is the finite central extension
`1 -> Z/N -> Gamma~ -> SL_2(Z[1/2]) -> 1` produced by their Corollary 1.3, and
the same holds for `SL_2(Z[1/p])` and a wide class of `S`-arithmetic groups.

**Why this belongs in the graph as its own node.**  It is the screen that says
the candidate is not already known to be hyperlinear.  Residually amenable
groups are sofic and hence hyperlinear, so a candidate that were residually
amenable would be dead on arrival; and `Gamma~` is an amalgamated free product
of virtually free groups over a finite index subgroup, a class for which
residual finiteness would otherwise be the default expectation.  The failure of
residual finiteness is what makes such an amalgam a live target at all.
