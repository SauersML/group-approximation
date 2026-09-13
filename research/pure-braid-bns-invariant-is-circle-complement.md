---
rg: 2
id: pure-braid-bns-invariant-is-circle-complement
kind: claim
title: "The BNS invariant of the pure braid group P_n is the complement of binom(n,3) + binom(n,4) P_3- and P_4-circles"
distinct_from:
  zaremsky-1-09-bnsr-invariants-of-pure-braid-groups: that claim is Zaremsky's question for every Sigma^m; this is the first invariant only, a literature theorem.
---

For every `n`, the BNS invariant `Sigma^1(P_n)` is the complement, in the
character sphere `S(P_n)`, of the union of the `P_3`-circles and the
`P_4`-circles, and there are exactly `binom(n,3) + binom(n,4)` such circles.

In the winding-number coordinates `chi = sum a_{ij} omega_{ij}` (equivalently
`chi(S_{ij}) = a_{ij}` on the standard generators):

- `chi` lies on the `P_3`-circle of `{i,j,k}` iff `a_{pq} = 0` unless
  `{p,q} <= {i,j,k}`, and `a_{ij} + a_{ik} + a_{jk} = 0`;
- `chi` lies on the `P_4`-circle of `{i,j,k,l}` iff `a_{pq} = 0` unless
  `{p,q} <= {i,j,k,l}`, `a_{ij} = a_{kl}`, `a_{ik} = a_{jl}`, `a_{il} = a_{jk}`,
  and `a_{ij} + a_{ik} + a_{il} = 0`.

Koban, McCammond and Meier, arXiv:1306.4046 (Groups Geom. Dyn. 9 (2015)).
Their Definition 4.3 and Theorem A; see the citation route. As they note, the
complement coincides with the real points of the first resonance variety of
the braid arrangement (Cohen–Suciu 1999, Proposition 6.9).
