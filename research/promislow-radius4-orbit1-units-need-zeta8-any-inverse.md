---
rg: 2
id: promislow-radius4-orbit1-units-need-zeta8-any-inverse
kind: claim
title: On one orbit of eight radius-four census supports, a characteristic-zero unit forces zeta_8 whatever its inverse support
distinct_from:
  promislow-radius4-support-pairs-need-zeta8: that fixes the inverse support to the census inverse support for all 52 supports; this removes that condition on the 8 supports of one orbit.
  promislow-inverse-has-equal-dihedral-syllable-length: that bounds the inverse support of every unit of K[P]; this uses the bound on 8 supports and decides every unit supported there.
  rational-unit-conjecture-torsion-free: that is the unit conjecture over Q for every torsion-free group; this is 8 supports on one group.
---

**ESTABLISHED.** Let `P` be the Promislow group in the model
`(s, t)(s', t') = (ss', t + s t')`, with `a = ((1,-1,-1),(1,1,0))` and
`b = ((-1,1,-1),(0,1,1))`. Let `S_1` be the 21-element set listed in
`research/artifacts/promislow-radius4-census-box-2026-09-13.md`. It is the
support of a nontrivial unit `u_0` of `F_2[P]` supported in the word ball
`B(4)`, one of the 52 (`promislow-radius4-one-sided-and-integral-separation`),
and `T_1 = supp(u_0^(-1))` has word radius 5. Let `Phi` be the eight
automorphisms `a -> a^(+-1), b -> b^(+-1)` and `a -> b^(+-1), b -> a^(+-1)`.
The eight sets `phi(S_1)` are census supports.

Let `K` be a field of characteristic zero, `phi in Phi`, and `u in K[P]` a
unit with `supp(u) in phi(S_1)`. If `u` is not `lambda g`, then
`supp(u^(-1)) in phi(T_1)`, and `K` contains a primitive eighth root of unity.

So no nontrivial unit of `Q[P]`, `R[P]`, `Q_2[P]` or `Z[P]` is supported in
any of these eight supports, whatever the support of its inverse.

The eight supports in the orbit of representative 0 are decided the same way
(`promislow-radius4-orbit0-units-need-zeta8-any-inverse`). The other 36 census
supports are covered only with the inverse support fixed
(`promislow-radius4-support-pairs-need-zeta8`). On their five representatives
the same computation left cases undecided at the time limit, ran out of
memory, or had not finished, as recorded in the artifact. Units supported in
`B(4)` outside the 52 supports, and anything at radius five, are not covered.

DERIVATION
[[promislow-radius4-orbit1-units-need-zeta8-any-inverse-proof]]
