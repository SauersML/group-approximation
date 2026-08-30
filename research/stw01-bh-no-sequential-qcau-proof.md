---
rg: 2
id: stw01-bh-no-sequential-qcau-proof
kind: route
title: Diagonalize against a compact approximate-unit sequence by one partial isometry
target: stw01-separable-ideal-does-not-force-sequential-qcau
requires: []
artifacts:
  - research/artifacts/stw01-sigma-unital-extension-audit-2026-08-30.md
---

It is enough to work with `K(H) triangleleft B(H)`.  Suppose `(e_n)` is any
positive-contractive sequential approximate unit for `K(H)`.  We construct
orthonormal sequences `(xi_k)`, `(eta_k)` and increasing indices `(n_k)`.

After the first `k-1` pairs have been chosen, choose `xi_k` orthogonal to
their span.  Approximate-unit convergence on the rank-one operator with
range `C xi_k` implies `e_n xi_k -> xi_k`, so choose `n_k>n_{k-1}` with

```text
||e_(n_k)xi_k-xi_k|| < 1/k.
```

The operator `e_(n_k)` is compact.  Hence there is a unit vector `eta_k`,
orthogonal to all vectors chosen so far, such that

```text
||e_(n_k)eta_k|| < 1/k.
```

At later stages choose every new vector orthogonal to the preceding ones.
Define a contraction `V in B(H)` by `V eta_k=xi_k` and by zero on the
orthogonal complement of the closed span of the `eta_k`.  Then

```text
||[e_(n_k),V]eta_k||
 = ||e_(n_k)xi_k-Ve_(n_k)eta_k||
 >= 1-2/k.
```

Thus `||[e_(n_k),V]||` does not converge to zero.  No sequential approximate
unit of `K(H)` can be quasicentral relative to `B(H)`, whether or not it is
increasing.  Taking the direct sum with `C` supplies the stated nonzero
bounded trace without changing the obstruction.
