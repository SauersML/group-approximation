---
rg: 2
id: xl-commuting-minimal-action-forbids-proximal-factors-proof
kind: route
title: Minimal subsets of a proximal square lie on the diagonal, and Gamma-orbits spread the agreement
target: xl-commuting-minimal-action-forbids-proximal-factors
requires: []
---

**Lemma.**  If `B` is proximal, every minimal closed `G`-invariant subset `N`
of `B x B` lies in the diagonal.  *Proof.*  Take `(b, b') in N` and a net `g_i`
with `g_i b -> c` and `g_i b' -> c`.  Then `(c, c) in N`, and by minimality
`N` is the orbit closure of `(c, c)`, which lies in the closed invariant
diagonal.

**Theorem.**  Let `pi : X -> B` be a continuous `G`-map.  By Zorn's lemma choose
a minimal closed `G`-invariant `M subset X`.  For `gamma in Gamma` the map
`x -> (pi(x), pi(gamma x))` is continuous and `G`-equivariant (as `gamma`
commutes with `G`).  The image of `M` is a compact `G`-invariant set that is
minimal (a continuous equivariant image of a minimal flow is minimal), so by
the Lemma `pi(gamma m) = pi(m)` for every `m in M` and `gamma in Gamma`.  Fix
`m in M`.  Then `pi` is constant on `Gamma m`, which is dense in `X` by
minimality of `Gamma`; continuity makes `pi` constant, equal to `b = pi(m)`.
Since `pi(g x) = g pi(x)`, `b` is fixed by `G`.  QED.

**Corollary 1.**  Let `X subset Y^Gamma` be nonempty closed, invariant under
the diagonal `G`-action and the shift, and `Gamma`-minimal.  The map
`x -> p(x(e))` is a continuous `G`-map `X -> B` (evaluation at `e` commutes
with the diagonal action).  By the Theorem it is constant with value a
`G`-fixed point of `B`, contradicting the hypothesis that `B` has none.

**Corollary 2.**  Compose `X -> Y -> B`; the composite is nonconstant because
a nontrivial boundary is minimal with no fixed point, contradiction.

**Corollary 3.**  Gromov boundaries of nonelementary hyperbolic groups, ends
of trees with nonelementary actions, and `G/P` for lattices `G` in semisimple
groups are boundaries (minimal and strongly proximal, hence proximal) without
fixed points.

*Sanity check.*  The Theorem does not forbid (CMA_G) outright: the proof only
uses proximality, and amenable `G`-spaces without proximal factors are not
excluded by it.  For amenable `G` the statement is consistent with examples
such as `G = Gamma = Z` acting on a torus by commuting irrational rotations,
where there is no nontrivial proximal factor.
