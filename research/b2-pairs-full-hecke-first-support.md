---
rg: 2
id: b2-pairs-full-hecke-first-support
kind: claim
title: The B2 arm pairs the first native sign exactly on the full Hecke source
artifacts:
  - research/b2-full-hecke-first-support-proof.md
  - experiments/full_q_b2_r_support_audit.py
distinct_from:
  native-j1-extension-gives-gl5-but-only-second-whitehead-gram: that leaves the first r sign free on the coarser p2 source under the bare GL5 stabilizer; this uses the additional literal B2 root which normalizes the finer full Hecke source Q and exchanges its two r signs.
  endpoint-whitehead-star-braid-synchronizes-native-gauges: that synchronizes the J1, J2, and endpoint reservoir gauges and gives an exact p2-level support fence when B2 is absent; this proves positive first support only after compression to the actual full source Q and does not identify the two reservoir gauges.
  full-moving-hecke-packet-retains-q-kernel-profile: that gives QWQ=0 in a complete L0, W, M, J1 representation; this proves that the orthogonal first sign cut inside Q has rank one half after adjoining the B2 action, a fact compatible with zero endpoint compression.
  b2-b3-pair-full-hecke-four-native-sectors: that also uses B3 to flip the second sign and proves a one-quarter common source for the two actual native compressions; this is the single-arm first-support calculation used in that joint theorem.
---

**ESTABLISHED REPRESENTATION-UNIVERSAL FULL-SOURCE SUPPORT.**  Retain the
actual common Hecke source

```text
Q=e_(L_0,lambda_0),
L_0=<H,d,f,c,k,v,w,s>                                (BFS1)
```

from `center-chain-mixed-hecke-overlap-is-common-pauli-source`, and put

```text
r=x_58(a_2),       B_2=x_84(b_2),       C_2=x_54(q). (BFS2)
```

Both `r` and `B_2` normalize the signed pair `(L_0,lambda_0)`, so they
reduce `Q`.  The ordinary Steinberg commutator row and the Leavitt
factorization `a_2b_2=q` give

```text
[r,B_2]=C_2,             B_2rB_2^(-1)Q=rC_2Q=-rQ.   (BFS3)
```

Consequently `B_2Q` exchanges the two spectral projections

```text
E_+=Q(1+r)/2,                  E_-=Q(1-r)/2.          (BFS4)
```

In every exact finite-dimensional representation of this packet,

```text
rank(E_+)=rank(E_-)=rank(Q)/2.                        (BFS5)
```

The first native Whitehead support on `p_2` is

```text
p_2(J_1p_2J_1)p_2=p_2(1+r)/2.
```

Since `Q<=p_2`, its restriction to the actual common source is therefore

```text
QJ_1p_2J_1Q=Q(1+r)/2=E_+,
rank(QJ_1p_2J_1Q)=rank(Q)/2.                          (BFS6)
```

Thus a surviving full Hecke source automatically pays a positive first
native support, with the sharp universal fraction `1/2`.  This does not
contradict the exact `p_2`-level zero-support profile: the latter omits the
full signed source and its `B_2` normalizer.  It also does not contradict
the exact full-packet profile with `QWQ=0`: the `B_2` pairing is internal
to the `r`-sign decomposition of `Q`, whereas `W` may still carry all of
`Q` out of itself.

No Property `(T)`, canonical trace, computation, literature input, or
Lean compilation is used.

DERIVATION
b2-full-hecke-first-support-proof
