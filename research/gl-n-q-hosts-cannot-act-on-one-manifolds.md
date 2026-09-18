---
rg: 2
id: gl-n-q-hosts-cannot-act-on-one-manifolds
kind: claim
title: No group acting faithfully on a one-manifold with finitely many components contains GL_n(Q) for n >= 3, and none acting on the line or an interval contains SL_2(Q)
distinct_from:
  germ-extensions-omit-standard-gl-n-q: that excludes standard (analytic) copies of GL_n(Q) from piecewise-projective and piecewise-affine groups and their germ extensions in any dimension; this excludes every copy, standard or not, but only from groups acting faithfully on one-manifolds.
  gl-n-q-embeds-in-fp-simple-group: that is the open embedding problem; this is an obstruction for one class of hosts.
  higman-group-embeds-in-no-piecewise-analytic-circle-group: that excludes Higman's group from piecewise-analytic circle groups; this excludes GL_n(Q), n >= 3, from all groups of homeomorphisms of one-manifolds.
  sl-n-z-circle-actions-factor-through-finite-groups: that is Witte's theorem on finite-index subgroups of SL(n,Z) acting on the circle; this is its consequence for hosts of GL_n(Q).
artifacts:
  - research/artifacts/gq-deep-pp-2-scope.md
---

**ESTABLISHED** through `gl-n-q-hosts-cannot-act-on-one-manifolds-proof` (a direct
corollary of Witte's theorem; lane-proved, not independently reviewed; no novelty
claimed).

**Statement.** Let `M` be a one-manifold (Hausdorff, second countable, possibly
with boundary) and `H <= Homeo(M)`.
1. If `M` has finitely many components, then `H` has no subgroup isomorphic to a
   finite-index subgroup of `SL(3,Z)`. So for every `n >= 3`, `H` contains no
   copy, standard or not, of `GL_n(Q)`, `SL_n(Q)`, `GL_n(Z)` or `SL_n(Z)`.
2. If `M` is connected and not a circle (`M` is `R`, `[0,1)` or `[0,1]`), then
   every element of finite order in `Homeo(M)` has order at most 2. So `H`
   contains no element of order 3, hence no copy of `SL_2(Z)`, `SL_2(Q)`, or
   `GL_n(Q)` for any `n >= 2`.

**Hosts excluded.** Every group that embeds in a group of homeomorphisms of the
circle, the line or an interval, whatever its action on the embedded copy, is
excluded for `n >= 3`. This includes Thompson's `F` and `T`, `T-bar`, the Stein
groups `F_{2,3}` and `T_{2,3}`, the Lodha--Moore groups and Monod's
piecewise-projective groups `H(A)` (which act on `R`), groups of PL or
piecewise-projective circle homeomorphisms, and `Homeo(S^1)` itself. Groups
acting faithfully on the line or an interval are excluded for `n = 2` as well.

**Not excluded.** Circle hosts for `n = 2`: `SL_2(Q)` acts faithfully on the
circle of rays in `R^2`. Hosts acting on Cantor sets (`V`-type groups, `nV`,
`VA`, groups over `P^1(Q_p)` or the adeles) or on manifolds of dimension at least
two are not touched; for those see O2--O4 of `gl-n-q-embeds-in-fp-simple-group`
and `germ-extensions-omit-standard-gl-n-q`.
