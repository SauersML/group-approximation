---
rg: 2
id: six-pair-chart-swap-retains-external-gauge
kind: claim
title: The combined original and moved Pauli charts retain an external Weyl gauge
artifacts:
  - research/six-pair-chart-swap-gauge-proof.md
  - experiments/six_pair_chart_swap_gauge_audit.py
distinct_from:
  external-weyl-dressed-native-pair-is-root-valued: that computes the exact root-valued relative word and observes that the external Weyl moves the Pauli chart; this adjoins both charts simultaneously and proves by a finite model that their combined factor still does not identify the external Weyl reservoir gauge.
  root-valued-overlap-does-not-undress-external-selector: that uses an abstract one-dimensional root-transporter packet; this realizes the literal two three-pair Pauli charts, their adjacent native scale actions, the chart swap, and the mixed commutant tests in one finite factor.
  six-generator-one-jump-router-has-s3-radical-atlas: that produces a six-generator Schur packet with a rank jump; this is a scoped six-Pauli-pair normalizer model and makes no affine or Schur-rank assertion.
---

On the carrier

```text
F=P_zP_C,             z=x_13(q),             C=x_42(q),
```

retain the original same-center arms

```text
A_m=x_(4,k_m)(a_m),       B_m=x_(k_m,2)(b_m)
```

and their images under `h=w_14(1)w_23(1)`:

```text
A'_m=x_(1,k_m)(a_m),      B'_m=x_(k_m,3)(b_m).        (SCG1)
```

The two triples have central commutators `C` and `z`.  Their only nontrivial
cross commutators are, for matching `m`,

```text
[A_m,B'_m]=R=x_43(q),       [A'_m,B_m]=S=x_12(q).     (SCG2)
```

The four roots `z,C,R,S` commute with one another and with every arm.  The
external Weyl swaps

```text
z <-> C,            R <-> S,            A_m <-> A'_m,
B_m <-> B'_m.                                            (SCG3)
```

Both native Whiteheads act on both charts by the same adjacent scale
permutation, and commute with `h`:

```text
W_1:(1 2),          W_2:(2 3),
W_1W_2W_1=W_2W_1W_2,          [h,W_i]=1.              (SCG4)
```

Equations `(SCG1)--(SCG4)` do not force the multiplicity gauge of `h`.
There is an exact finite model on six qubits in which

* `(A_m,B_m)` are the first three independent Pauli pairs;
* `(A'_m,B'_m)` are the last three independent Pauli pairs;
* `z=C=-I` and `R=S=+I`;
* `W_i` simultaneously perform the indicated adjacent swap in both
  three-qubit blocks; and
* `h=H_chart tensor D`, where `H_chart` swaps the two three-qubit blocks and
  `D=-1` is a scalar multiplicity involution.

All covariance rows, `(SCG3)--(SCG4)`, and `h^2=1` hold exactly.  The marked
root is `-I`, so it survives.  For the root-valued pair

```text
g_1=W_1,             g_2=hW_2,
```

the cross-Gram is full and the relative word sends `z` to `C`.  But after
removing the canonical label actions, the two reservoir gauges are

```text
V(g_1)=+1,             V(g_2)=-1.                    (SCG5)
```

They are not unitarily conjugate on any nonzero subcorner.  The relative
gauge in `(SCG5)` is scalar, so every mixed commutator with all six Pauli
pairs vanishes exactly.  Hence adding the moved chart does not turn the
root-valued scalar overlap into the shared native gauge required by the
two selector rows.

This is a scoped model of the displayed combined-chart action table, not a
representation of the full binary-Leavitt Steinberg group.  In particular,
an additional odd ordinary-word relation involving the elementary factors
of `h` could exclude the scalar sign.  No such relation currently attaches
that external Weyl word to the prescribed row-two `1/8` selector occurrence.
Thus the sharp next target remains an occurrence-typed chart bridge which
also fixes the external Weyl gauge; six-pair factoriality and mixed
commutators alone do not do so.

No Property `(T)`, Kazhdan input, canonical trace, literature theorem,
local computation, or Lean compilation is used.

DERIVATION
six-pair-chart-swap-gauge-proof

