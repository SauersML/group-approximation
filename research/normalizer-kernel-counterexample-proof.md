---
rg: 2
id: normalizer-kernel-counterexample-proof
kind: route
title: Tensor the monomial Cartan of the regular S3 algebra and shift it
target: normalizer-kernel-generation-is-not-automatic
requires: []
---

Under Fourier decomposition,

```text
L(S_3) = C direct_sum C direct_sum M_2(C).
```

Choose the eigenbasis of the normal `C_3` in the standard two-dimensional
representation.  Every standard-representation matrix of `S_3` is monomial
in this basis: `C_3` is diagonal and a transposition swaps the two eigenlines.
Therefore

```text
D = C direct_sum C direct_sum D_2
```

is a maximal abelian subalgebra normalized by every canonical `S_3` unitary.
Those unitaries generate `L(S_3)`, while a canonical group unitary belongs to
`D` exactly for an element of `C_3`.  Thus `L(C_3)` is a proper
three-dimensional subalgebra of the four-dimensional algebra `D`.

Let `B` be the tracial infinite tensor product of copies of `L(S_3)` indexed
by `Z`, let `A` be the corresponding tensor product of the `D`'s, and let the
shift act on both.  Then

```text
M = B rtimes Z = L(S_3 wr Z).
```

The lamp unitaries normalize the site Cartans and generate `B`; the shift
unitary normalizes `A`; together they generate `M`.  The tensor product of the
site MASAs is maximal abelian in `B`.  For a nonzero shift Fourier coefficient,
commutation with cylinder projections at coordinates separated from their
translates forces that coefficient to vanish (equivalently, the Bernoulli
shift is properly outer relative to the tensor Cartan).  Hence
`A' cap M=A`.  The displayed normalizers generate `M`, so `A` is Cartan.

The wreath product is amenable and ICC, hence `M` is the hyperfinite `II_1`
factor.  A canonical group unitary belonging to `A` cannot have nonzero shift
coordinate; for a finite lamp configuration, tensor slice maps show that it
belongs to `A` exactly when every lamp lies in `C_3`.  Consequently

```text
lambda(Gamma) cap U(A) = lambda(C_3^((Z))),
W*(lambda(Gamma) cap U(A)) = tensor_Z L(C_3) proper subset tensor_Z D=A.
```

This proves `(NKF1)` in a diffuse factor.

