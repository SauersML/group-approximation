---
rg: 2
id: binary-leavitt-el20-arbitrary-profile-native-cross-gram
kind: claim
title: The two native binary transports overlap on every surviving EL20 operator-norm profile
distinct_from:
  binary-leavitt-arbitrary-profile-native-cross-gram: that states the corresponding theorem for St20 and therefore retains a possible central Steinberg-lift phase; this works directly in the manuscript's elementary-group lane, where the order-seven anchors are literal matrix identities.
  binary-leavitt-native-two-scale-cross-gram-positive: that is a canonical-trace normalized-HS claim; this is quantified over every arbitrary normalized trace profile arising from a norm-corona representation.
---

**OPEN DIRECT-ELEMENTARY MF CROSS-GRAM CLAIM.**  Every norm-matrix-corona
homomorphism from

```text
G=EL_20(L_(F_2)(1,2))
```

which retains `z=e_13(s_1t_1)` has, after positive-density active
reblocking, two actual native unequal-scale transports

```text
S_1,S_2:P_source H_n -> P_target H_n
```

and constants `gamma,c>0` satisfying

```text
tr_n(S_1^*S_2S_2^*S_1)>=gamma tr_n(P_source)-o(1),
tr_n(P_source)>=c,                                      (EAP1)
```

with the two mixed source-Pauli commutators of the relative polar gauge
tending to zero.  The transports must be the prescribed rows with ratios
`1/2 -> 1/4` and `1/4 -> 1/8`, not unrelated rectangular completions.

The quantifier is over arbitrary operator-norm profiles.  Canonical group
trace moments, Property `(T)`, Kazhdan correction, and literature inputs are
not available.

## Attempts

The original order-seven route through one common reducing cut is refuted:
`el20-order-seven-heads-force-zero-common-hecke-reducing-cut` forces that cut
to vanish, and `order-seven-first-exit-is-not-seven-step-leakage` shows that
the proposed one-exit estimate did not control a seventh-power telescope.

The surviving route is
`order-seven-growing-multicut-gives-el20-native-cross-gram`.  Its only open
input is `growing-multicut-el20-order-seven-inheritance`, but moving cuts do
not by themselves finish the argument.  The exact fence
`moving-order-seven-stage-gauges-have-coboundary-drift` shows that seven
transported conjugates of one nontrivial gauge may have trivial cyclic
product.  The live requirement is therefore an EL20 coefficient-sensitive
fixed-Hecke-frame lock (equivalently, asymptotic commutation with the
reservoir holonomy), in addition to the moving boundary control.
