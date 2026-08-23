---
rg: 2
id: two-grading-cz-gauge-has-a-balanced-intertwiner-absorber
kind: claim
title: The two-grading CZ gauge has an exact balanced-intertwiner absorber
distinct_from:
  controlled-pauli-corner-has-clifford-groupification: that classifies one CZ implementer as `CZ tensor V` and notes that covariance cancels `V`; this tests the proposed positive/negative two-grading use inside the Fano Julia commutator and gives an exact leakage countermodel.
  shared-gauge-cz-cancellation-needs-an-identity-outer-anchor: that proves packet-word parity cannot produce `I tensor V` as a separate anchor; this grants the two desired diagonal blocks outright and shows they still do not cancel against an unconstrained Julia off-diagonal block.
  fano-hybrid-reflection-has-a-universal-regular-hs-gap: that gives a regular-trace obstruction to one ordinary hybrid word; this is a finite-dimensional marked Pauli counterpacket for the proposed sector-entangled covariance escape.
---

Let `C=CZ` be the four-dimensional controlled-Z involution, with eigenvalue
multiplicities `(3,1)`. Let `V` be a balanced involution on a `2m`-dimensional
multiplicity space, with `m` positive and `m` negative eigenvalues. On two
equal grading halves put

```text
R_+=C tensor V,             R_-=I_4 tensor V,
R=diag(R_+,R_-).                                      (TGC1)
```

This is exactly the proposed shared-gauge normal form: the positive block
carries `CZ tensor V`, the negative block carries `I tensor V`, and `R^2=1`.
The two blocks have identical spectra:

```text
mult_(+1)(R_+)=mult_(-1)(R_+)=4m
                    =mult_(+1)(R_-)=mult_(-1)(R_-).   (TGC2)
```

Hence there is a unitary `U` with `U R_+ U^*=R_-`. Define the grading and
Julia reflection

```text
z=diag(I,-I),
j=[[0,U^*],[U,0]].                                    (TGC3)
```

Then `j=j^*=j^(-1)`, `zjzj=-I`, and

```text
[R,j]=0,                    RjRj=I.                   (TGC4)
```

Nevertheless, with

```text
Q=((I-C)/2) tensor I_(2m) <= H_+,
S=P_+ j P_-,                                        (TGC5)
```

the forbidden row has full expected mass

```text
||QS||_(2,H_+)^2=tr_(H_+)(Q)=1/4                     (TGC6)
```

(or `1/8` in the normalized trace of both grading halves).

Thus the shared multiplicity involution does not cancel in the Fano payment
commutator merely because it appears on both diagonal blocks. It conjugates
the representation-dependent off-diagonal Julia block, and that block may
intertwine `CZ tensor V` with `I tensor V` exactly. The covariance packet,
the two-grading relations, `R^2=1`, and the marked D8 relation all hold while
the proposed commutator defect is zero and the uncovered row is positive.

To make the two-grading construction useful one must independently force the
Julia off-diagonal block to commute with the common gauge `V`, or produce the
literal identity-outer anchor and multiply it out before forming the Julia
row. Either requirement is precisely the same-reservoir multiplicity
coupling isolated by `shared-gauge-cz-cancellation-needs-an-identity-outer-anchor`;
it is not supplied by Stone--von Neumann uniqueness or by the CZ normalizer
relations.
---
