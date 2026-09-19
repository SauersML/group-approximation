---
rg: 2
id: spectral-low-energy-shrunk-space-obstruction
kind: claim
title: A shrunk low-energy intertwiner space forbids a small-defect unitary
---

Let `L` be a positive semidefinite self-adjoint operator on the Hilbert space
`M_d(C)` with normalized Hilbert--Schmidt inner product.  Write

```text
E(T) = <T, L T>.
```

For `a>0`, let `K_a` be the spectral subspace of `L` for eigenvalues in
`[0,a]`.  Suppose `K_a` has a shrunk subspace `X <= C^d` with

```text
dim X - dim K_a(X) >= gamma d.                       (SLS1)
```

Then every unitary `U` satisfies the quantitative energy floor

```text
E(U) >= a gamma.                                     (SLS2)
```

Equivalently, if a unitary has `E(U)<=delta`, then **every** low-energy matrix
space `K_a` with `a>delta/gamma` has no `gamma d`-shrunk subspace.

For mixed representation problems one takes

```text
E(T)=sum_(s in S) ||rho(s)T-T sigma(s)||_2^2.
```

Thus the nonlinear finite-multiplicity selection step can be recast as a
noncommutative-rank question about the spectral low-energy intertwiner space.
This strictly refines zero-one Wedderburn support: `K_a` may retain only the
cheap singular directions *inside* a block.  A linear-size shrunk subspace is
then a proof-carrying obstruction detectable by operator-scaling / shrunk-
subspace algorithms, while `shrunk-matrix-space-unitary-distance` supplies the
dimension-free analytic endpoint.