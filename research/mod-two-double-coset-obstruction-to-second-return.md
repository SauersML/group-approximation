---
rg: 2
id: mod-two-double-coset-obstruction-to-second-return
kind: route
title: Separate the two orbital types modulo two and read the A2 correction word
target: first-root-parahoric-target-has-a-distinct-double-coset-type
requires:
  - first-root-parahoric-incidence-has-a-two-to-four-morita-lift
  - raw-denominator-incidence-kills-off-diagonal-shell-orbit
  - two-path-holonomy-is-paid-by-corner-leakage
---

Diagonal `C`-orbits on ordered pairs of `D`-cosets are classified by
`D backslash C/D`, giving `(DCT2)--(DCT3)`.  Reduction modulo two sends the
target representative `x_13(2)` to the identity and the source
representative `x_12(1)` outside the subgroup `Dbar`.  A subgroup and a
double coset represented outside it are disjoint, proving `(DCT5)` and the
absence of every integral return.

For minimality, `d=x_23(2)` belongs to `D` and the standard type-`A_2`
commutator is `[x_12(1),x_23(2)]=x_13(2)`.  This is a two-edge expression,
while `(DCT5)` rules out one edge.  Rearrangement gives the exact section
correction `a=bd` with `d in D`; compression by a `D`-central projection
therefore makes their endpoint projections identical.  Their transport
holonomy is the internal corner unitary `PdP`, which has canonical normalized
trace zero.  The two-path leakage identity charges it conditionally on a
compression-to-average relation; the section equality alone does not provide
that extra linear incidence.
