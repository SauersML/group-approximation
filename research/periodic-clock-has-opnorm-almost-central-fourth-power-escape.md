---
rg: 2
id: periodic-clock-has-opnorm-almost-central-fourth-power-escape
kind: claim
title: Periodic clocks have almost-central unitary fourth powers far from their joint commutants
artifacts:
  - research/periodic-clock-fourth-power-escape-proof.md
distinct_from:
  periodic-clock-p-commutant-has-uniform-joint-gap: that proves a dimension-free correction after exact P-commutation; this proves that the exactness hypothesis cannot be replaced by a merely vanishing P-commutator, even for unitaries which are literal fourth powers.
  higman-fourth-return-jointly-centralizes-clock: that forces the actual matcher return K^4 to almost commute with P and D; this gives almost-central fourth powers with no matcher attached, showing why simultaneous centrality alone cannot finish that argument.
---

**ESTABLISHED.**  Let `q_n=3^n` and let `(P_n,D_n)` be the periodic clock
packet

```text
D_n e_x=exp(2 pi i x/q_n)e_x,
P_n e_x=e_(2^(-1)x).                                 (ACE1)
```

There are unitaries `R_n,C_n` with `C_n=R_n^4` such that

```text
||[C_n,P_n]||_op ->0,
||[C_n,D_n]||_op ->0,                                (ACE2)
```

but

```text
dist(C_n,{P_n,D_n}') >=1                             (ACE3)
```

for every sufficiently large `n`.

The construction is already supported on the primitive unit shell
`span{e_x:x in (Z/3^nZ)^*}`.  On that reducing shell the exact joint
commutant is scalar, and `(ACE3)` remains valid with the same lower bound.

Thus the pair `(P_n,D_n)` has no dimension-independent operator-norm
almost-commutant correction theorem, even on unitary fourth powers.  The
uniform theorem `periodic-clock-p-commutant-has-uniform-joint-gap` really
uses exact commutation with `P_n`; the factor `3^n r_n` in its approximate
corollary cannot simply be deleted by appealing to simultaneous
almost-centrality.

This does not construct a Higman matcher.  The fourth root `R_n` below does
not satisfy `R_n P_n R_n^* approximately D_n`.  Therefore the result fences
one proposed completion of the matcher argument while leaving open whether
the **same** fourth root can be both a spectral matcher and a slow
almost-central return.
