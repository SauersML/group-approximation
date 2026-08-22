---
rg: 2
id: transitive-control-normalizer-forces-projectively-equal-payloads
kind: claim
title: A transitive full-matrix control normalizer has only projectively equal payload blocks
distinct_from:
  transitive-controller-orbit-common-twist-preserves-zero-lcu: that positively factors a common twist once the intended payload controllers already form one symmetry orbit; this proves full-matrix covariance can create such an orbit only when its payload blocks are projectively equivalent.
  grading-zero-corner-does-not-orient-controlled-payload: that finds an independent orientation in one binary controlled gate; this grants one shared orientation across every branch and proves that finite-control covariance then forbids a nontrivial SELECT payload.
  packet-dressed-shared-implementer-requires-one-outer-class: that classifies two normalizers by outer class; this is the direct full-matrix block calculation for an arbitrary transitive control register.
  central-corner-block-is-not-a-group-word: that excludes constructing a controlled sum from its commuting control and payload words; this excludes the proposed covariance implementation even after granting a new normalizing word.
---

Let `V=C^m`, let the finite transitive control packet act irreducibly on
`V`, and hence let its complex linear span be `M_m(C)`.  On `V tensor H`
consider a block-diagonal unitary

```text
T=diag(AU_1,...,AU_m),                                  (TCN1)
```

where `A,U_i in U(H)`.  If `T` normalizes the control algebra
`M_m(C) tensor 1`, then there are phases `lambda_i` and one unitary `U` with

```text
U_i=lambda_i U.                                         (TCN2)
```

Consequently compression to any prepared control vector `xi` is only

```text
(|xi><xi| tensor 1)T(|xi><xi| tensor 1)
 =|xi><xi| tensor A U sum_i |xi_i|^2 lambda_i.           (TCN3)
```

It cannot be `A` times a nontrivial average of independently prescribed
payload words.

## Proof

For every matrix unit `e_ij`, normalization gives

```text
T(e_ij tensor 1)T^*=e_ij tensor A U_i U_j^* A^*
                    in M_m(C) tensor 1.                 (TCN4)
```

Therefore every `U_i U_j^*` is scalar.  Fixing `j=1` gives `(TCN2)`, and
direct compression gives `(TCN3)`.

The same proof applies when the control is presented by any finite group:
irreducibility and Burnside's theorem make the span of its image the full
matrix algebra.  The statement here is exact; using it for approximate
microstates first requires the usual finite-packet normalized-HS
exactification.

## Consequence for common-orientation LCU

The proposed shared factor is algebraically useful: if an ordinary word
really evaluated as `diag(Aw_i)`, its uniform-corner compression would be
`A(m^-1 sum_i w_i)`, so zero and normalized HS norm would be orientation
independent, exactly as in
`transitive-controller-orbit-common-twist-preserves-zero-lcu`.  The theorem
shows that a finite transitive **full-matrix** control packet cannot force
that word by covariance unless all `w_i` are projectively the same.

One may enlarge the normalized base so that the decorated matrix units
`e_ij tensor w_iw_j^*` are present.  Then `(TCN4)` no longer normalizes the
finite control algebra, and the finite-packet Schur argument no longer
forces one common multiplicity actor `A` in arbitrary representations.
Equivalently, a wreath product has the intended induced module with the
desired SELECT operator, but its other Mackey types need not use the same
payload representation or the same active control orbit.  Selecting that
one induced type with positive canonical density is precisely the existing
selected-corner/multiplicity-return gate.

Thus common orientation removes the sign ambiguity **after** SELECT exists,
but finite transitive covariance cannot construct SELECT without either
making its payload trivial or reintroducing representation-wide type
selection.
