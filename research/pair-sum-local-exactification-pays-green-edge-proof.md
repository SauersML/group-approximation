---
rg: 2
id: pair-sum-local-exactification-pays-green-edge-proof
kind: route
title: Exact local pair-sum faces pay the entire intrinsic Green edge field
target: parity-charged-green-edge-curl-coercivity
requires:
  - fixed-parity-faces-exactify-with-loewner-row-square-control
  - pair-sum-faces-have-row-square-incidence-control
  - normalized-occurrence-equality-transfer-preserves-face-gap
  - row-square-equality-variance-transfers-averaged-pinching-gap
  - low-odd-square-removes-pairwise-green-stationarity
---

Work with the normalized augmented-face occurrence weights.  First apply
fixed-face Loewner exactification to the retained occurrence contractions
`X_(f,i)`, obtaining commuting parity reflections `A_(f,i)`.  In each
logical-coordinate cloud form the stationary weighted average `S_i` of
the `A_(f,i)` and put `Q_i=sgn(S_i)`.  The operator-valued cloud Poincare
inequality and weighted sign estimate then give

```text
 E_inc=(1/I) sum_f sum_(i in f)||Q_i-A_(f,i)||_2^2
      <=C(E_equality+E_sparse).                           (PEG1)
```

To see this without a maximum-over-occurrences loss, first expand every
cloud edge difference `A_u-A_v` through `A_u-X_u`, `X_u-X_v`, and
`X_v-A_v`.  The operator square inequality bounds its weighted row square
by a fixed multiple of equality energy plus the local correction row
square.  Cloud Poincare controls the variance about `S_i`; the exact
weighted sign identity `(WPT1)` controls the incidence displacement from
`A_u` to `Q_i`.  Finally `(LFE3)` controls the local correction.  Its finite
word symmetrization costs only a fixed constant in trace: for every
positive residual square `H` and every contraction word `w`,

```text
 tr(w^* H w)=tr(H^(1/2)ww^*H^(1/2))<=tr(H).
```

The row-square pair-sum congestion theorem now applies to these exact local
copies and the shared candidates:

```text
 H_pair=(1/L^2)sum_(i,j)[Q_i,Q_j]^*[Q_i,Q_j]
       <=C H_inc^sym,

 E_pair=tr(H_pair)
       <=C E_inc
       <=C(E_equality+E_sparse).                          (PEG2)
```

Only the traced consequence is used here.  Although the first line is a
Loewner inequality, its endpoint-conjugacy symmetrization is not asserted
to be covariant under the original presentation, because the shared
`Q_i` can be analytic signs of cloud averages.  Tracial invariance removes
all those endpoint conjugates with no loss and requires no additional
physical spectral cut.

It remains only to compare the finite-Green edge signal with the ordinary
commutator.  Put `U_ij=Q_iQ_j`.  Since the `Q_i` are reflections,

```text
 [Q_i,Q_j]=U_ij-U_ij^(-1),
 omega_ij=(U_ij^(-2)-U_ij^2)/4
         =-(U_ij+U_ij^(-1))[Q_i,Q_j]/4.
```

The two factors are polynomials in the same unitary, and
`||U_ij+U_ij^(-1)||_infinity<=2`.  Consequently

```text
 ||omega_ij||_2^2<=1/4||[Q_i,Q_j]||_2^2.                 (PEG3)
```

Equivalently, the exact identity
`omega_ij^*omega_ij=R_ij(I-R_ij)` with
`R_ij=[Q_i,Q_j]^*[Q_i,Q_j]/4` gives the same estimate.
After normalized summation, `(PEG1)`--`(PEG3)` prove the stronger bound

```text
 E_edge(omega)<=C(E_equality+E_sparse).                  (PEG4)
```

Thus `(PCG1)` follows without using its nonnegative divergence term.  This
does not assert that ordinary triangle curl is quadratic.  Its linear code
tangent is charged exactly by the face/equality incidence correction in
`(PEG1)`; hence it is consistent with
`ordinary-green-triangle-curl-has-a-linear-code-tangent`.
