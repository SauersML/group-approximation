---
rg: 2
id: adjoint-parity-defects-form-tanner-fundamental-cone
kind: claim
title: Exact parity puts every adjoint commutator row in the Tanner fundamental cone
distinct_from:
  unique-neighbor-ldpc-checks-force-dense-noncommutation: that controls the zero versus nonzero support; this proves the quantitative homogeneous inequalities obeyed by squared HS magnitudes.
  operator-unique-neighbor-cosystolic-rounding: that asks for a correction to a joint PVM; this identifies the exact classical cone available before the operator bootstrap.
---

Let the reflections `(Q_i)_(i in T)` commute in every parity check `T` and
have product one.  On `L_2(M)`, put

```text
C_i=Ad(Q_i).
```

The `C_i` are commuting orthogonal involutions on every check and
`prod_(i in T)C_i=I`.  For every `v in L_2(M)`, define

```text
x_i(v)=||(I-C_i)v||_2^2.                                  (APD1)
```

Then, for every check `T` and every `i in T`,

```text
x_i(v) <= sum_(k in T, k!=i) x_k(v).                       (APD2)
```

Indeed, use the common spectral PVM of the commuting involutions.  On each
joint character atom, `prod C_i=I` says that an even number of the signs are
negative.  Therefore the indicator that sign `i` is negative is bounded by
the sum of the other negative-sign indicators.  Integrating against the
spectral measure of `v` and multiplying by four gives `(APD2)`.

Taking `v=Q_j` gives

```text
x_i(Q_j)=||Q_iQ_j-Q_jQ_i||_2^2,                            (APD3)
```

so every squared-commutator row belongs to the classical Tanner fundamental
cone.  Classical expander-code pseudoweight bounds can therefore be imported
as magnitude-spreading estimates.  They remain homogeneous and do not by
themselves produce a same-Hilbert commuting correction or align the spectral
pieces belonging to different rows.
