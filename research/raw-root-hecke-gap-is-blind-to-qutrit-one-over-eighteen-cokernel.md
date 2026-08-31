---
rg: 2
id: raw-root-hecke-gap-is-blind-to-qutrit-one-over-eighteen-cokernel
kind: claim
title: The full raw-root Hecke packet has an exact qutrit one-over-eighteen cokernel
distinct_from:
  two-raw-roots-have-a-uniform-full-carrier-gap: that controls distance to the full-carrier intertwiner space; this places the absorber exactly inside that space
  rectangular-safe-covariance-has-a-positive-head-absorber: that uses a free multiplicity factor at arbitrary rational density; this tensors the literal 288-element qutrit regular packet to the two-root finite Toeplitz carrier
  finite-same-trace-tags-have-a-commutant-or-absorber-dichotomy: that proves the general finite-tag dichotomy; this gives the simultaneous Hecke-plus-qutrit exact model
---

Let

```text
F_N=GL_(28N)(F_2),                     N>=2,
F_0=<C,H,C_1,W>,                       |F_0|=288,
q_b=E e_b,                             tau_(F_0)(q_b)=1/18.
```

For every unitary representation `beta:F_N->U(V)` there are
finite-dimensional representations `Pi_S,Pi_T` of
`F_N times F_0` and an isometry `S:H_S->H_T` such that

```text
Pi_T(g,u)S=S Pi_S(g,u)                 for all (g,u),
TS=I,                     ST=I-Q,
tr_(H_T)(Q)=1/18.                                           (HQH1)
```

The target restriction to `F_0` is a multiple of its left regular
representation, so all canonical qutrit weights and the value
`tau(Ee_b)=1/18` are retained exactly. The head `Q` is right
convolution by `q_b` in the qutrit factor.

In particular every constant-core and both raw-root covariance terms in
the packet `Q_N` vanish:

```text
Pi_T(r)S-SPi_S(r)=0                    for every r in Q_N. (HQH2)
```

Thus the property-T estimate for the two raw roots returns
`dist(S,Hom_(F_N))=0`, while the cokernel still has density `1/18`.
The Hecke theorem is sharp but cannot see multiplicity.

After the usual target/source grading is added, the rectangular actor and
the grading generate a `D_8` image commuting with
`F_N times F_0`. Hence the entire simultaneous packet has finite image,
a quotient of

```text
F_N times F_0 times D_8.                                  (HQH3)
```

The abelian head-torus variant makes the head literally equal to the
left packet atom `Ee_b`; the full `F_0` variant makes it the
commuting right copy with the same rank. Therefore a finite qutrit
same-trace authentication, even placed on top of the complete two-root
Hecke gap, does not expose the rectangular cokernel. One mixed relation
must identify left and right packet position while also consuming a raw
Jacobson occurrence.

DERIVATION
tensor-the-hecke-carrier-with-the-qutrit-regular-bimodule-proof
