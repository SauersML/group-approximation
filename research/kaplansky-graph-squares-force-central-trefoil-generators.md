---
rg: 2
id: kaplansky-graph-squares-force-central-trefoil-generators
kind: claim
title: A 4-cycle in the Kaplansky graph of a support-3 zero divisor makes the support subgroup a centrally extended quotient of the trefoil group
distinct_from:
  zero-divisor-support-subgroup-host-constraints: that lists ambient properties a host must lack; this derives a specific central element and a presentation from one 4-cycle of the Kaplansky graph.
  small-non-up-left-support-has-no-orderable-quotient: that forbids orderable quotients of the support subgroup; this is used here, together with a 4-cycle, to force a central extension with a rational second Betti number.
  f2-support-three-zero-divisors-need-support-at-least-22: that bounds support sizes by exhaustive search over F_2; this is a structural consequence of one short cycle over every field.
artifacts:
  - research/artifacts/zds-three-support-theory-2026-09-13.md
---

**ESTABLISHED.** Let `G` be torsion-free, `k` a field, and `alpha, beta`
nonzero in `k[G]` with `alpha beta = 0` and `|supp alpha| = 3`. Choose
`beta` of least support, left-translate so that `1 in supp alpha`, and put
`H = <supp alpha>`. Suppose the Kaplansky graph `K_k(alpha, beta)`
(Abdollahi--Taheri, arXiv:1612.00934, §2) contains a 4-cycle. Then:

1. `H = <u, v>` for two elements with `u^3 = v^2 = z != 1`. So `z` is central
   in `H` and has infinite order.
2. `H = B / N`, where `B = <u, v | u^3 = v^2>` is the trefoil knot group,
   `N` is a nontrivial normal subgroup with `N ∩ <u^3> = 1`, and `H` is not
   isomorphic to `B`.
3. `Q = H / <z>` is an infinite quotient of `<u, v | u^3, v^2>`, the modular
   group, and the images of `u` and `v` have orders exactly `3` and `2`.
4. `H^ab` is finite and `dim_Q H_2(Q; Q) >= 1`.

So a 4-cycle forces the support subgroup to be a torsion-free central
extension, by `Z`, of an infinite proper quotient of `PSL(2, Z)` with
positive second rational Betti number.

**Relation to the source.** Item 1 is A--T Thm C4 ("then there exist
non-trivial group elements `x` and `y` such that `x^2=y^3` and either
`{1,x,y}` or `{1,y,y^{-1}x}` is the support of a zero divisor"), with `u = y`
and `v = x`. In each of their nine cases the substituted pair generates
`<h_2, h_3>`. The route re-derives the classification of 4-cycle relations
independently of their tables. Items 2--4 are not stated in the sources read.
No novelty is claimed.

**Consequence.** If `H` has no nontrivial central element, or more generally
if the centralizer of every nontrivial element of `G` is cyclic, the
Kaplansky graph has no 4-cycle
(`cyclic-centralizer-hosts-have-square-free-kaplansky-graphs`).

DERIVATION
[[kaplansky-graph-squares-central-trefoil-proof]]
