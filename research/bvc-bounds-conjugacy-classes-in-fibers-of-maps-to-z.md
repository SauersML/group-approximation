---
rg: 2
id: bvc-bounds-conjugacy-classes-in-fibers-of-maps-to-z
kind: claim
title: A group with BVC meets boundedly many conjugacy classes in every nonzero fiber of a homomorphism to Z
---

**Statement.** Let `G` have property BVC with witness `V_1, ..., V_n`, and let `phi: G -> Z`
be a homomorphism. Put `C = sum over the i with phi(V_i) != 0 of |V_i ∩ ker phi|`, a finite
number. Then for every integer `m != 0`, the elements `g` with `phi(g) = m` lie in at most
`C` conjugacy classes of `G`.

**Corollary (twisted conjugacy).** If `G = K ⋊_alpha Z` and `phi` is the projection, then for
every `m >= 1` the Reidemeister number `R(alpha^m)` (the number of `alpha^m`-twisted conjugacy
classes of `K`) is at most `m·C`. So `R(alpha^m)` grows at most linearly in `m`.

**Relation to the literature.** The case `m = 1` in qualitative form, "infinitely many twisted
classes rules out BVC", is von Puttkamer–Wu arXiv:1607.03790, Lemma 1.19 (and Corollary 1.20
for property `R_infinity`). The new content is the bound, uniform over all fibers.

**Calibration.**

- `Z^r ⋊_A Z` with `A` hyperbolic: `R(A^m) = |det(1 - A^m)|` grows exponentially, so there is
  no BVC. This was already known (virtually solvable: 1607.03790, Proposition 1.12).
- `Z[1/2] ⋊_2 Z`: `R(alpha^m) = |Z[1/2]/(2^m - 1)| = 2^m - 1`, so there is no BVC (known).
- The bound alone does not force virtual cyclicity: `osin-group-times-z-has-bvc` has BVC and
  maps onto `Z`, with `R(id^m) = 2` for all `m`.
