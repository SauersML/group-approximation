---
rg: 2
id: cyclic-centralizer-groups-have-no-support-three-zero-divisors
kind: claim
title: In a torsion-free group with cyclic centralizers, no element with support of size three is a zero divisor
distinct_from:
  kaplansky-zero-divisor-conjecture: that is the conjecture over every torsion-free group and every support size; this is support size three in a host class that contains the hyperbolic groups without unique products.
  cyclic-centralizer-hosts-have-square-free-kaplansky-graphs: that is an established girth bound for the Kaplansky graph in these hosts; this is the nonexistence statement itself.
artifacts:
  - research/artifacts/zds-three-support-theory-2026-09-13.md
---

**OPEN.** Let `G` be a torsion-free group in which the centralizer of every
nontrivial element is cyclic, for example a torsion-free hyperbolic group.
Then for every field `k`, no `alpha in k[G]` with `|supp alpha| = 3` is a
zero divisor.

**Why this host class.**
- It contains every torsion-free hyperbolic group. Among those are the only
  known torsion-free groups without unique products where the zero-divisor
  conjecture is not known:
  - the generalized Rips--Segev groups;
  - the Gruber--Martin--Steenbock groups;
  - the Arzhantseva--Steenbock groups (arXiv:1407.2441, Thm `main` and
    Cor `C: T`), which are torsion-free, hyperbolic, and some have
    Property (T).
- Steenbock asks (arXiv:1307.0981, introduction): "Do Rips-Segev groups
  satisfy Kaplansky's zero-divisor conjecture?"
- The other known non-unique-product groups are covered already. Passman's
  and Promislow's are solvable, and Carter's are virtually `Z^k x F_m`; the
  Arzhantseva--Steenbock introduction records both facts.

## Attempts

1. **Short cycles (established).** A least counterexample has a Kaplansky
   graph with no cycle of length at most 4
   (`cyclic-centralizer-hosts-have-square-free-kaplansky-graphs`). Over `F_2`
   the graph is cubic, so its girth is at least 5.
2. **5-cycles (established census).** Every 5-cycle reads one of two
   relators up to automorphism
   (`cyclic-centralizer-host-pentagons-have-two-relation-orbits`). The census
   does not exclude them.
3. **6-cycles (census only).** 233 of 351 classes are unrecognized. So local
   cycle relations alone will not finish the argument. A proof has to combine
   cycles or use global structure.
4. **Positive cones (established).** A counterexample
   `alpha = r_0 + r_1 x + r_2 y` needs positive relations in each of
   `{x^-1, y^-1}`, `{x, y^-1 x}` and `{y, x^-1 y}`
   (`zero-divisor-support-vertex-cones-contain-positive-relations`). In a
   hyperbolic host, ping-pong on attracting fixed points of loxodromic
   elements would rule out a positive relation in a pair. Nothing forces the
   pairs of a zero divisor to be in ping-pong position.
5. **Search restricted to girth 5 (not run).** Over `F_2`, the landed search
   `zds3.c` could be run on the connected cubic graphs of girth at least 5
   (`nauty-geng -c -f -d3 -D3`), a small fraction of the triangle-free ones.
   With the per-graph sieves extended to torus and `BS(m, n)` relations, that
   would push the support bound in these hosts past the general one. The
   graph counts and the cost at 24 vertices were not measured here.

**Exact gap.** A global argument excluding a cubic Kaplansky graph of girth
at least 5 whose 5-cycles read the two remaining relators, in a torsion-free
group with cyclic centralizers.
