---
rg: 2
id: two-transport-cross-gram-has-a-fixed-mass-reducing-corner
kind: claim
title: Two approximate transports produce a fixed-mass approximately reducing cross-Gram corner
distinct_from:
  mixed-intertwiner-energy-transport-localization: that decomposes one unitary intertwiner among exact representation blocks; this composes two possibly rectangular contractions and cuts their cross-Gram operator without a block decomposition.
  pauli-overlap-yields-positive-spectral-corner: that extracts a corner from one already established Pauli overlap mass; this additionally transports every shared source generator to the corner with explicit error.
  lin-state-dependent-gh-preserves-the-commutant: that exactifies one approximate finite-group representation on an amplification; this is a same-matrix finite-dimensional cross-Gram and spectral-cut lemma before any exactification.
---

Let `H_B=C^d` be a source space and `H_A=C^D` a possibly different target
space.  Normalize every rectangular Hilbert--Schmidt norm by the source
dimension `d`, so `||T||_(2,B)^2=d^(-1)Tr(T^*T)`.  Let `S` be finite, let
`A_s in U(H_A)`, `B_s in U(H_B)`, and let
`T_1,T_2:H_B->H_A` be contractions.  Put

```text
epsilon_(i,s)=||A_s T_i-T_i B_s||_(2,B),
G=T_1^*T_2,                  H=G^*G,
m=||G||_2^2,                D=sum_s(epsilon_(1,s)+epsilon_(2,s)).
                                                               (TCG1)
```

For every `s in S`, one has

```text
||B_s^* G B_s-G||_2 <= epsilon_(1,s)+epsilon_(2,s),  (TCG2)
||B_s^* H B_s-H||_2 <= 2(epsilon_(1,s)+epsilon_(2,s)).
                                                               (TCG3)
```

If `m>0`, there is a threshold `t in [m/4,m/2]` such that the spectral
projection

```text
P=1_[t,1](H)                                           (TCG4)
```

satisfies

```text
tau_d(P)>=m/2,
sum_s ||[P,B_s]||_2^2 <= 8D/m.                        (TCG5)
```

Thus a fixed lower bound on cross-Gram mass gives a fixed-density common
source corner which is approximately reducing for every shared right-hand
packet generator.  In particular the conclusion applies literally to two
isometries from one physical space into a common induced or dilated target;
no equality of source and target dimensions is needed.

The dependence in `(TCG5)` is deliberately stated in the unsquared
transport errors.  Equivalently, if
`E_i=sum_s epsilon_(i,s)^2`, then

```text
sum_s ||[P,B_s]||_2^2
 <= (8 sqrt(|S|)/m)(sqrt(E_1)+sqrt(E_2)).              (TCG6)
```

Without a spectral gap for `H` at a prescribed threshold, the resulting
commutator norm therefore has the expected fourth-root dependence on the
original squared transport energy.  A linear-in-energy spectral-projection
claim does not follow from these hypotheses.

If, in addition, the packet has a commutant Poincare estimate

```text
dist_2(Z,{B_s:s in S}')
 <= kappa^(-1)(sum_s||[Z,B_s]||_2^2)^(1/2),           (TCG7)
```

then there is an exactly reducing projection `P_0 in {B_s:s in S}'` with

```text
||P-P_0||_2 <= (4 sqrt(2)/kappa)sqrt(D/m),             (TCG8)
tau_d(P_0)>=m/2-(4 sqrt(2)/kappa)sqrt(D/m).            (TCG9)
```

In particular, on an already authenticated odd-congruence packet with a
uniform Selberg commutant gap, positive cross-Gram mass really does select
a positive exact reducing corner in the same matrix dimension.
