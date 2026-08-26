---
rg: 2
id: head-square-whitehead-loop-preserves-deep-star-flag
kind: claim
title: The head-square Whitehead cube is an odd fixed-flag loop but moves the Pauli chart
artifacts:
  - research/head-square-whitehead-loop-proof.md
distinct_from:
  asymmetric-head-reflection-return-erases-deep-flags: that proves inverse-conjugate returns reduce every deep flag to one half; this gives an odd return that preserves every all-positive deep flag, but isolates its forked-chart gauge.
  native-whitehead-hecke-head-has-order-seven-anchor: that uses the nonreducing product J_i H_i and an order-seven relation; this uses the reducing head square H_i^2 and the outer-corrected Whitehead U_i in an order-three moving-chart loop.
  support-return-gives-gauged-native-loop: that constructs support-idempotent Whitehead returns through alternate prefix charts; this is the shorter literal head-square identity on the positive distinct-center star.
  binary-leavitt-two-shared-gauge-selector-compiler: that needs the corrected Whitehead gauge itself attached to the unequal source flag; this loop preserves the source flag but constrains only a product with the prefix-root and outer-Weyl chart gauges.
---

For one adjacent pair of marked-star cells, retain

```text
H_i=B_(i+1)A_i,              H_i^2=X_i,
J_i=X_iY_iX_i,               U_i=L_iJ_i,              (HSW1)
```

where `L_i` is the matching outer-coordinate Weyl.  The middle and outer
coordinate packets commute.  Since `X_i,Y_i` are the two elementary
involutions of `SL_2(F_2)`,

```text
(X_iJ_i)^3=(Y_iX_i)^3=1.
```

Consequently the following are exact elementary-group identities:

```text
(H_i^2U_i)^3=L_i,              (U_iH_i^2)^3=L_i.      (HSW2)
```

This is an actual odd occurrence of `U_i`, not a formal cancellation of
the order-four head as a Coxeter involution.

The loop preserves the useful star source flags.  On the two adjacent
anchored `Z` arms,

```text
Ad(H_i^2U_i):
  Z_i |-> Z_(i+1),
  Z_(i+1) |-> Z_iZ_(i+1).                              (HSW3)
```

Thus the atom `Z_i=Z_(i+1)=+1` is invariant.  The other heads and corrected
Whiteheads on a longer star fix the all-positive atom in the remaining
`Z` signs, so `(HSW2)` restricts without leakage to the literal quarter
source, and also to the eighth source after adjoining the next cell.

The identity still does not isolate the desired corrected-Whitehead gauge.
The prefix root `X_i=H_i^2` does not normalize the fixed anchored Pauli
packet.  It sends

```text
A_(i+1) |-> A_(i+1) F_i,
F_i=x_(alpha_(i+1),k_i)(a_i),                          (HSW4)
```

where `F_i` is the forked arm with the new outer index and old middle
index.  It is not one of the anchored `A` arms.  The outer Weyl `L_i`
similarly transports between the anchored and forked charts.  Hence the
three stages in `(HSW2)` are a closed groupoid loop on the fixed `Z` atom,
not three copies of one operator in a fixed full-Pauli chart.

After choosing charts, the reservoir equation has the form

```text
(D_(X_i)D_(U_i))_2 (D_(X_i)D_(U_i))_1
 (D_(X_i)D_(U_i))_0 = D_(L_i),                        (HSW5)
```

with transition conjugacies between stages.  It does not imply
`D_(U_i)=1`, nor identify `D_(U_i)` with the cumulative asymmetric-head
holonomy.  A finite moving-chart `S_3` model permits a nontrivial
involutive corrected-Whitehead gauge while the product around `(HSW5)` is
the prescribed outer-Weyl transition.

Thus `(HSW2)` is an explicit odd return that genuinely preserves the
quarter/eighth star flag.  The remaining seam is smaller than
a support-return problem: one additional cross-chart occurrence must
identify the forked arm `F_i` with the anchored arm in the same reservoir
frame, or provide an identity-outer copy of either `D_(X_i)` or `D_(L_i)`.

The identities are asserted in the elementary image.  Using their written
lifts in the unquotiented Steinberg group still requires the usual central
`K_2` lift check.  No Property `(T)`, Kazhdan input, canonical trace,
computation, or literature theorem is used.

DERIVATION
head-square-whitehead-loop-proof
