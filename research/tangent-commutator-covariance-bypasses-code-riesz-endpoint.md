---
rg: 2
id: tangent-commutator-covariance-bypasses-code-riesz-endpoint
kind: claim
title: Tangent commutator covariance bypasses the code-Riesz endpoint
distinct_from:
  complete-overlay-row-newton-is-a-code-riesz-multiplier: that treats the coordinate coboundary on arbitrary two-form arrays and isolates a vector-valued endpoint multiplier; this uses the exact covariance of arrays in the actual reflection-tangent range, where the coordinate mask is the identity.
  code-laplacian-has-uniform-cp-green-approximants: that supplies the scalar CP Green polynomial; this proves that the preceding divergence map is already completely contractive on tangent commutator residuals.
  involution-augmented-code-jacobian-adds-no-cb-loss: that splits normal and tangent variables; this closes the linear cb assembly on its tangent summand to any fixed contraction accuracy.
---

ESTABLISHED.  Let `S_1,...,S_L` be commuting reflections and let
`h_i=h_i^*` be tangent to the reflection manifold, so

```text
 S_ih_iS_i=-h_i.
```

Write the raw linearized commutator and its standard tangent trivialization

```text
 r_ij=[h_i,S_j]+[S_i,h_j],
 b_ij=-(1/2)S_iS_jr_ij.                                (TCB1)
```

Differentiating the exact reflection identity

```text
 Q_j[Q_i,Q_j]Q_j=-[Q_i,Q_j]
```

at the commuting tuple gives `S_jr_ijS_j=-r_ij`.  Since the `S_i`
commute, the trivialized residual has the same covariance:

```text
 S_jb_ijS_j=-b_ij.                                     (TCB2)
```

Hence the coordinate odd projection

```text
 P_j=(I-Ad(S_j))/2
```

acts as the identity on `b_ij`.  The masked divergence in `(CRM2)` is
therefore simply

```text
 C(b)_i=(1/L)sum_j b_ij.                               (TCB3)
```

It is completely contractive in both normalized row and column norms.  For
example, operator Jensen gives

```text
 (1/L)sum_i C(b)_i^*C(b)_i
 <=(1/L^2)sum_(i,j)b_ij^*b_ij,                         (TCB4)
```

and the analogous inequality holds with the factors reversed, at every
matrix amplification.

On a code-character block with difference support `T`, `(TCB3)` equals the
code Laplacian applied to the perturbation modulo the simultaneous-
conjugation gauge:

```text
 C(Dh)=Delta(h-h_gauge),       Delta=|T|/L.             (TCB5)
```

Compose `(TCB3)` with the CP Green polynomial
`G_K=sum_(t<K)A^t` from
`code-laplacian-has-uniform-cp-green-approximants`.  The resulting
finite-time right inverse has cb row/column norm at most `K` and leaves
linear residual at most

```text
 (1-delta)^K                                                (TCB6)
```

in normalized Hilbert--Schmidt norm off the gauge kernel.  Choosing one
fixed `K=O_delta(log(1/eta))` gives any prescribed contraction factor
`eta<1`, uniformly in code length, matrix dimension, and multiplicity.
Newton needs such a fixed contraction, not the endpoint limit `K->infinity`.
Thus `(CRM3)` for arbitrary arrays is unnecessary for the exact-base
linear step.

The raw covariance survives the contraction-valued extension with a
controlled forcing error.  For selfadjoint contractions `X_i,X_j`, put
`R_ij=[X_i,X_j]` and `E_j=I-X_j^2`.  Direct expansion gives

```text
 X_jR_ijX_j+R_ij=E_jX_iX_j-X_jX_iE_j,                 (TCB7)
```

so its `L_2` norm is at most `2||E_j||_2`.  Multiplication by the bounded
tangent-normalization factors changes only the numerical constant.
Therefore the positive involution residual created by aggregate block
compression is exactly the vanishing normal-forcing term in this
finite-time tangent inverse.

This closes the exact-base linear cb gate.  The remaining nonlinear basin
problem is to implement the finite-time correction before an exact code
character decomposition exists and show that sparse parity/equality
re-exactification preserves its strict contraction.
