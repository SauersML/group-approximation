---
rg: 2
id: duplicate-selector-transports-retain-occurrence-seam
kind: claim
title: Duplicated selector transports retain the occurrence seam
invalidates:
  - duplicated-arm-whitehead-hecke-closes-native
distinct_from:
  literal-selector-roots-force-center-chain: that treats one incidence chain whose cross commutators directly expose the selector roots; this proves that duplicating the arms either recreates that obstruction or introduces two uncontrolled occurrence transports.
  literal-prefix-three-root-swap-retains-typed-carriers: that audits one direct prefix Whitehead actuator; this combines that typed-corner fence with the common-versus-separate transporter dichotomy and the Hecke cut.
  same-center-whitehead-gram-is-not-native-selector-gram: that refutes the maximal Gram of two same-center adjacent swaps with the wrong label rank; this covers arbitrary duplicated literal cross roots and the direct unequal-prefix Whitehead alternative.
---

Duplicating the anchored arms does not by itself authenticate the two native
selector occurrences.

First let `A_m,B_(m+1)` be the cross-commuting arms in `(ARC3)`.  If one
common group word `r` transports both arms to duplicates, then

```text
[rB_(m+1)r^(-1),rA_mr^(-1)]
 =r[B_(m+1),A_m]r^(-1)=1.                              (DAS1)
```

Hence a nonzero root carrying `b_(m+1)a_m` cannot be obtained from the
cross-commuting anchored pair by one common Weyl or Whitehead transport.
Composable duplicates require two separate words `r_B,r_A`; after moving
back to the anchored carrier, every comparison contains the relative word

```text
v=r_B^(-1)r_A.                                         (DAS2)
```

No cancellation in `(DAS1)` controls `v`.  Proving that it preserves the
selected carrier and aligns the two arm gauges is exactly an additional
occurrence-holonomy assertion, not a consequence of duplicating the roots.
If the duplicates are instead retained as complete authenticated Heisenberg
cells and their cross commutator is made nonzero, the incidence calculation
of `literal-selector-roots-force-center-chain` applies to those duplicate
cells verbatim: their consecutive centers do not form the simultaneous
reducing Pauli packet.

Second, one may avoid a cross commutator and build the selector coefficient
directly.  Put

```text
x_1=s_(00)t_0,          y_1=s_0t_(00),
x_2=s_(000)t_(00),      y_2=s_(00)t_(000).
```

Then `y_ix_i` and `x_iy_i` are the source and target prefix idempotents, and
the characteristic-two Whitehead words

```text
J_i=E_(p_i,q_i)(x_i)E_(q_i,p_i)(y_i)E_(p_i,q_i)(x_i) (DAS3)
```

are literal full group unitaries implementing the two partial swaps.  This
is precisely the actuator audited by
`literal-prefix-three-root-swap-retains-typed-carriers`: `(DAS3)` swaps the
two equal minimal corners but does not identify the depth-one and depth-two
packet identities on which the `1/4` and `1/8` selector normal forms are
required.

Finally let `e` be any finite-character atom supported on a root packet
centralized by both `J_i`.  Then `S_i=J_ie` are unitaries on `eH`, and

```text
S_1^*S_2S_2^*S_1=e,
tau(S_1^*S_2S_2^*S_1)=tau(e).                         (DAS4)
```

Equation `(DAS4)` is maximal but tautological: it holds for every two full
unitaries reducing `e`.  It does not identify the two typed prefix packet
units or the unequal controlled selector occurrences.  This is the same
typing failure isolated by
`same-center-whitehead-gram-is-not-native-selector-gram`, now after the
duplicated-arm construction.

Thus the proposed duplicated-arm/Whitehead-Hecke route does not establish
the native cross-Gram claim.  A successful duplicated construction must add
a genuinely matrix-dependent reducing subcorner and a quantitative relation
controlling `(DAS2)` there; a disjoint compatible character atom and fixed
algebraic occurrence words are insufficient.

DERIVATION
duplicate-selector-occurrence-seam-proof
