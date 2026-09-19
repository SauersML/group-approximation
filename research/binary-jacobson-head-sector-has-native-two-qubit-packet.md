---
rg: 2
id: binary-jacobson-head-sector-has-native-two-qubit-packet
kind: claim
title: The Jacobson head sector carries a native two-qubit Pauli packet
artifacts:
  - research/binary-jacobson-native-two-qubit-proof.md
distinct_from:
  binary-jacobson-head-root-has-opnorm-square-decoder: that asks for a matrix-selected same-square Toeplitz return; this proves that the surviving head cut already carries the full transverse degree-four label factor, leaving only the return occurrence unauthenticated.
  four-pauli-standard-polynomial-gives-a-fixed-rectangular-gap: that gives the analytic PI gap for an abstract two-qubit tuple; this identifies four literal Jacobson root words which realize that tuple on the marked sector.
  leavitt-heisenberg-branch-doubles-character-multiplicity: that studies an entire coefficient Heisenberg group under a Morita compressor; this uses two fixed rank-three root triangles and no compressor.
---

**ESTABLISHED.**  Put

```text
J=F_2<S,T | TS=1>,          Q=1-ST,
E=EL_5(J),                  w=x_13(Q),

X_0=x_12(Q),   Z_0=x_23(1),
X_1=x_14(Q),   Z_1=x_43(1).                              (J2Q1)
```

These five literal group elements generate a fixed extraspecial two-group:
all four `X_i,Z_i` are involutions, `w` is a central involution,

```text
[X_0,Z_0]=w=[X_1,Z_1],                                  (J2Q2)
```

and every cross-pair commutator is trivial.  Consequently, in every
finite-dimensional unitary representation `rho` of this packet, the
projection

```text
P=(1-rho(w))/2                                           (J2Q3)
```

reduces all four words.  If `P!=0`, then on `P C^d`

```text
rho(X_0)rho(Z_0)=-rho(Z_0)rho(X_0),
rho(X_1)rho(Z_1)=-rho(Z_1)rho(X_1),                     (J2Q4)
```

and the two pairs commute with one another.  They therefore generate an
exact copy of

```text
M_2(C) tensor M_2(C) tensor I_m ~= M_4(C) tensor I_m,   (J2Q5)
```

for some `m>=1`.  In particular `4` divides `rank(P)`, and the literal tuple

```text
(rho(X_0),rho(Z_0),rho(X_1),rho(Z_1))|_P                (J2Q6)
```

has degree-four standard-polynomial operator norm `8`, unchanged by the
spectator `I_m`.

This packet is robust in operator norm with a dimension-independent modulus.
It is fixed and finite, so sufficiently accurate evaluations of `(J2Q1)--
(J2Q2)` may be exactified; if the rounded head cut is nonzero, the corrected
tuple satisfies `(J2Q4)--(J2Q6)` on that cut.

Thus the **target fullness** clause of the sparse PI route is already native
inside the binary Jacobson rank-five group.  The first pair alone gives the
source degree-two factor.  By
`opnorm-common-intertwiner-pi-gap-is-sparse-terminal`, the remaining
Property-`(T)`-free MF problem is reduced further: authenticate one common
matrix-selected occurrence `R` which intertwines four source-factor
contractions with the four literal words in `(J2Q6)`.  No positive-density
estimate, target bicommutant theorem, or spectator elimination remains.

The identity inclusion of the first pair is not such an occurrence: it does
not transport the other two Pauli words into the first `M_2` factor.  This is
why the native packet alone is consistent in the regular representation and
does not prove head-root collapse.

DERIVATION
binary-jacobson-native-two-qubit-proof
