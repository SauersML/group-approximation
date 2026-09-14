---
rg: 2
id: hyperbolic-bounded-finite-quotients-iff-quotientless-hyperbolic
kind: claim
title: An infinite hyperbolic group with finite quotients of bounded order exists iff one without finite quotients exists
distinct_from:
  hyperbolic-group-without-finite-quotients: that asks for an infinite hyperbolic group with no nontrivial finite quotient; this shows the weaker-looking demand of uniformly bounded finite images is equivalent to it
  sp21-lattice-hyperbolic-quotient-without-finite-quotients: that asks for a quotient of one fixed lattice without finite quotients; this is the elementary equivalence showing that any mechanism bounding the finite images of a hyperbolic quotient already produces such a group
---

**ESTABLISHED** (elementary; no novelty claimed).

For a finitely generated group `Q` the following are equivalent:

1. the orders of the finite quotients of `Q` are bounded;
2. the profinite completion `Q^` is finite;
3. `Q` has a finite-index normal subgroup `Δ` with no nontrivial finite quotient.

When they hold, `Δ` is the intersection of all finite-index subgroups of `Q`,
and `|Q/Δ|` is the largest order of a finite quotient of `Q`. If moreover `Q` is
infinite and word-hyperbolic, then `Δ` is an infinite word-hyperbolic group with
no nontrivial finite quotient.

**Consequence.** Some infinite hyperbolic group has finite quotients of bounded
order exactly when `hyperbolic-group-without-finite-quotients` holds, and hence,
through `kapovich-wise-rf-iff-finite-quotients`, exactly when some hyperbolic
group is not residually finite.

## What it rules out

- **Image-size mechanisms are not easier than the target.** Any argument that
  forces every finite quotient of a hyperbolic quotient `Γ/M` to factor through
  one fixed finite group (for example an image-size bound extracted from
  relative property (T)) is equivalent to producing a hyperbolic group without
  finite quotients, one finite-index step away.
- **The bound cannot come from a residually finite host.** For a residually
  finite `Γ`, such as an arithmetic `Sp(2,1)` lattice, the finite quotients of
  `Γ` itself have unbounded order. So a bound for `Γ/M` has to be created
  entirely by the relators in `M`.

Proof: `hyperbolic-bounded-finite-quotients-proof`.
