---
rg: 2
id: stw63-free-product-universal-norm-proof
kind: route
title: Push universal implementing unitaries through every pair representation
target: stw63-universal-free-product-test
requires: []
---

The forward implication follows by applying the universal assertion to the
codomain `F` and its canonical pair.

Conversely, let `phi,psi:Z->B` be unital embeddings.  The universal property
of the full unital free product gives a unital homomorphism

```text
pi:F->B,                 pi i_0=phi,   pi i_1=psi.
```

If unitaries `u_n in F` approximately conjugate `i_0` to `i_1`, then the
unitaries `pi(u_n)` approximately conjugate `phi` to `psi`, by contractivity
of `pi`.  No injectivity or exactness of `pi` is needed.

It remains to verify the scalar norm test.  If `(u_n)` implements approximate
equivalence, every summand in the definition of `Delta` tends to zero and is
bounded by `2^(1-k)`.  A finite-head/tail estimate therefore gives

```text
sum_k 2^(-k)||u_n i_0(z_k)u_n* - i_1(z_k)|| -> 0,
```

so `Delta=0`.

Conversely, if `Delta=0`, choose `u_n` for which the displayed sum is less
than `1/n`.  For each fixed `k`,

```text
||u_n i_0(z_k)u_n* - i_1(z_k)|| < 2^k/n.
```

Thus conjugacy holds on the dense sequence, and contractivity extends it to
every element of `Z`.  Hence the canonical embeddings are approximately
unitarily equivalent.
