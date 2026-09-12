---
rg: 2
id: galois-invariance-totally-real-atoms-proof
kind: route
title: Move the eigenvalue by the Galois action and use that a self-adjoint operator has real spectrum
target: galois-invariance-forces-totally-real-atoms
requires: []
---

Let `A in M_n(Z[G])` be self-adjoint, `T = r_A` its right multiplication
operator on `l2(G)^n`, and `lambda in Qbar` an atom,
`delta = dim_(N(G)) ker(T - lambda) > 0`. Fix `sigma in Gal(Qbar/Q)`.

**Step 1, the Galois action moves only the eigenvalue.** `A - lambda I` lies in
`M_n(Qbar[G])`, and the coefficients of `A` are rational integers, so they are
fixed by `sigma`. Hence

```text
sigma(A - lambda I) = A - sigma(lambda) I.
```

**Step 2, invariance.** By hypothesis, applied to `B = A - lambda I`,

```text
dim_(N(G)) ker(T - sigma(lambda)) = dim_(N(G)) ker(T - lambda) = delta > 0.
```

This is conclusion 2 of the target, for every conjugate that is real; it also
says the kernel is nonzero for every conjugate whatever its position.

**Step 3, total reality.** Suppose some conjugate `sigma(lambda)` is not real.
`A` is self-adjoint, so `T` is a bounded self-adjoint operator on `l2(G)^n` and
its spectrum is contained in `R`. For `z` off the real axis, `T - z` is
invertible with `||(T - z)^(-1)|| <= 1/|Im z|`, so `ker(T - z) = 0` and

```text
dim_(N(G)) ker(T - sigma(lambda)) = 0,
```

contradicting Step 2. So every conjugate of `lambda` is real, which is
conclusion 1. QED

**Remark on the two conclusions.** Step 3 uses nothing about masses, only that
a nonzero kernel is impossible off the real axis; Step 2 alone gives the equal
masses. So the hypothesis yields a constraint on the *location* of algebraic
atoms and not only on their multiplicities, and the location constraint is the
one a finite computation can violate.
