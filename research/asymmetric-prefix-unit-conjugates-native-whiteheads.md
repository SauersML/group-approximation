---
rg: 2
id: asymmetric-prefix-unit-conjugates-native-whiteheads
kind: claim
title: An asymmetric prefix-code unit exactly conjugates the two native Whiteheads
artifacts:
  - research/asymmetric-prefix-unit-whitehead-conjugacy-proof.md
distinct_from:
  literal-prefix-coupling-of-j1-j2-has-gl7-model: that uses two external root factors to compile the depth-two coefficients and admits a finite GL7 specialization; this uses one genuine binary-Leavitt prefix-code unit and an ordinary EL20 torus conjugator.
  compression-preimage-whitehead-preserves-gauge: that applies the Hilbert-hotel compression endomorphism and proves its preimage chain retains the Whitehead gauge; this uses an inner coefficient conjugacy between two particular prefix arrows and produces an exact raw-Whitehead mixed square.
  mixed-whitehead-cell-moves-signed-source: that transports a depth-two detector cell by a product of endpoint and native Whiteheads; this directly conjugates the first raw native Whitehead to the second and records its exact source and target Grams.
  binary-leavitt-arbitrary-profile-native-cross-gram: that requires both transports on one fixed positive Hecke frame; the occurrence here moves the quarter source and leaves the conjugator reservoir gauge uncontrolled.
---

**ESTABLISHED EXTERNAL MIXED-OCCURRENCE CANDIDATE.**  In the binary
Leavitt algebra put

```text
u=s_00t_0+s_01t_10+s_1t_11,
u^(-1)=s_0t_00+s_10t_01+s_11t_1.                     (APU1)
```

The domain code `{0,10,11}` and range code `{00,01,1}` are both complete,
so `u` is a unit.  For the two native coefficient pairs

```text
x_1=s_00t_0,       y_1=s_0t_00,
x_2=s_000t_00,     y_2=s_00t_000,                    (APU2)
```

prefix cancellation gives

```text
u x_1 u^(-1)=x_2,          u y_1 u^(-1)=y_2.         (APU3)
```

Let `h_(i,k)(u)` be the ordinary elementary torus word obtained from the two
Weyl words `w_(i,k)(u)` and `w_(i,k)(1)`, and put

```text
D=h_(8,10)(u)h_(7,11)(u).                             (APU4)
```

Conjugation by `D` applies `a |-> u a u^(-1)` to both root subgroups
`x_87(a)` and `x_78(a)`.  Let `P` be the product of constant Weyl words
implementing the coordinate cycle `7 |-> 8 |-> 9 |-> 7`, and define

```text
G=PD.                                                  (APU5)
```

For the literal native Whiteheads

```text
J_1=x_87(x_1)x_78(y_1)x_87(x_1),
J_2=x_98(x_2)x_89(y_2)x_98(x_2),                      (APU6)
```

one has the exact ordinary EL20 mixed square

```text
GJ_1G^(-1)=J_2,             GJ_1=J_2G.               (APU7)
```

In any exact finite-dimensional representation, let

```text
F=Q(1+r)(1+l)/4
```

be the literal full-Hecke quarter source and put `F'=GFG^(-1)`.  Then the
rectangular occurrence `C=GF` has exact Grams

```text
C^*C=F,                    CC^*=F',                   (APU8)
```

and its restriction to the raw native output has the exact square

```text
(GJ_1F)^*(GJ_1F)=F,
(GJ_1F)(GJ_1F)^*=J_2F'J_2,
GJ_1F=J_2F'G.                                         (APU9)
```

Thus `(APU7)--(APU9)` are a genuine full-group source-and-target-Gram-typed
comparison of the two raw native Whitehead occurrences.  They are absent
from the finite five-node parabolic packet because `u` uses the asymmetric
complete prefix codes in `(APU1)`.

This does **not** establish the arbitrary-profile native cross-Gram.  The
target source is the moved projection `F'`, not the original `F`, and no
present relation identifies the multiplicity frame of `G` with the fixed
Hecke frame.  In reservoir notation `(APU7)` gives conjugacy of the two raw
gauges through the gauge of `G`; it permits an arbitrary coboundary.  A
successful continuation must either prove positive fixed-frame incidence
between `F` and `F'` with an odd return that removes this gauge, or compose
`G` with another ordinary occurrence whose total source returns to `F` and
whose reservoir factor cancels.

No Property `(T)`, canonical-trace substitution, computation, or literature
theorem is used.

DERIVATION
asymmetric-prefix-unit-whitehead-conjugacy-proof
