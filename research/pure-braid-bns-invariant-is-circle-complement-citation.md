---
rg: 2
id: pure-braid-bns-invariant-is-circle-complement-citation
kind: route
title: Import the Koban–McCammond–Meier computation of Sigma^1 of the pure braid groups
target: pure-braid-bns-invariant-is-circle-complement
requires: []
---

Citation import, not a reproof. Read from the PDF of arXiv:1306.4046v1 on
2026-09-13.

- Theorem A (p. 1), verbatim: "The BNS-invariant for the pure braid group
  `P_n` is the complement of a union of `P_3`-circles and the `P_4`-circles in its
  character sphere. There are exactly `binom(n,3) + binom(n,4)` such circles."
- Definition 4.3 (p. 11), verbatim in substance: `chi` is part of a
  `P_3`-circle iff "all the endpoints of edges in `K_chi` belong to a three
  element subset `{v_i, v_j, v_k}` and the value of `chi(S_{ijk})` is zero";
  `chi` is part of a `P_4`-circle iff "all the endpoints of edges in `K_chi`
  belong to a four element subset `{v_i, v_j, v_k, v_l}`, the equations
  `chi(S_{ij}) = chi(S_{kl})`, `chi(S_{ik}) = chi(S_{jl})`, `chi(S_{il}) = chi(S_{jk})`
  hold and the sum of these three shared values is zero". Here `K_chi` is the
  graph of surviving standard generators (Definition 3.1).
- The proof is Theorem 4.4 (the circles lie in the complement, via natural
  projections and the map `P_4 -> P_3` of Lemma 2.9) plus Theorem 5.7 (every
  other character lies in the invariant).

The winding-number coordinates in the claim body use `chi(S_{ij}) = a_{ij}`,
which is how Zaremsky (arXiv:1507.08597, Section 3.1) matches `omega_{ij}` to
the standard generators.
