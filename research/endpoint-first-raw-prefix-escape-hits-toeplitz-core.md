---
rg: 2
id: endpoint-first-raw-prefix-escape-hits-toeplitz-core
kind: claim
title: The first raw zero-prefix escape has no marked finite-tail closure and reaches the Toeplitz core
artifacts:
  - research/endpoint-first-raw-prefix-toeplitz-threshold-proof.md
distinct_from:
  endpoint-zero-tail-packet-has-marked-finite-model: that retains the two stationary tails under all three native Whiteheads, the four center-chain arms, and the inward-outward endpoint crossings; this identifies the first already-named raw coefficient that leaves that model and proves that no finite tail enlargement can retain the mark.
  leavitt-first-offdiagonal-core-is-marked-non-lef: that starts from the diagonal elementary group and two abstract same-position raw roots and proves a fixed finite-table obstruction; this locates those roots as literal occurrences in the endpoint compiler and proves the sharp finite-tail escape before identifying the generated core.
  binary-jacobson-active-cycle-generates-rank-three: that reaches the Jacobson core from one balanced shift and a directed constant three-cycle; this reaches the rank-five Jacobson core from the diagonal elementary subgroup and the literal raw prefix/inverse-prefix occurrences already present in the endpoint construction.
---

**ESTABLISHED RAW-PREFIX THRESHOLD.**  In the prefix representation of the
binary Leavitt ring let

```text
alpha=000...,                 beta=1000...,
K=<alpha,beta>,               q=s_1t_1.
```

The returned-root occurrence

```text
T_0=x_97(t_0)
```

preserves `K^20`.  The word-length-one prefix occurrence

```text
L_y=x_87(s_0),                                      (RPE1)
```

already named in the literal `J_1`--`J_2` prefix compiler, does not:

```text
s_0 beta=01000... notin {alpha,beta}.                (RPE2)
```

This failure cannot be repaired by replacing the two tails with a larger
finite tail set.  If `F` is a finite set of infinite binary tails and
`span(F)^20` is invariant under `(RPE1)`, then `s_0F subseteq F`.  The only
finite orbit of the prefix injection `omega |-> 0omega` is `{alpha}`.
Consequently `F subseteq {alpha}` and `q span(F)=0`.  Thus no finite common
tail carrier invariant under `L_y` retains the actual mark `x_13(q)`.

Moreover the natural continuation is already the one-branch hard core, not
another finite endpoint model.  On the five coordinates

```text
I={1,3,7,8,9}
```

let `D` be the binary Cantor diagonal and `Lambda_I=EL_I(D)`.  Put

```text
H=<Lambda_I,T_0,L_y>.
```

Constant Weyl elements in `Lambda_I` move both raw roots to every ordered
root position.  Root addition and ordinary three-index commutators then give

```text
H=EL_I(<D,s_0,t_0>).                                  (RPE3)
```

In particular `H` contains

```text
EL_I(F_2<s_0,t_0 | t_0s_0=1>),                        (RPE4)
```

the full rank-five binary Jacobson elementary group, and contains the mark
`x_13(1-s_0t_0)=x_13(q)`.  Every homomorphism from `H` to a finite group
kills this mark, because its restriction to `(RPE4)` does.  Hence adjoining
the first raw forward prefix does not extend the two-tail marked finite
model: together with the already-used raw inverse prefix and the manuscript's
diagonal elementary packet, it crosses immediately to the existing
Toeplitz/Jacobson hard core.

This is an exact boundary result, not an operator-MF collapse.  The remaining
question is precisely the Property-`(T)`-free MF-invisibility of the
Jacobson head root; no smaller finite-tail repair lies between the endpoint
packet and that hard problem.

No Property `(T)`, Kazhdan input, stability theorem, trace hypothesis,
literature input, computation, or Lean compilation is used.

DERIVATION
endpoint-first-raw-prefix-toeplitz-threshold-proof

