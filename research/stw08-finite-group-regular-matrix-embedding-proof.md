---
rg: 2
id: stw08-finite-group-regular-matrix-embedding-proof
kind: route
title: Put the finite regular covariant representation inside one AF matrix amplification
target: stw08-finite-group-crossed-products-preserve-af-embeddability
requires: []
artifacts:
  - research/artifacts/stw08-af-embedding-status-and-coherence-audit-2026-08-30.md
---

Let `alpha:F->Aut(A)` be the action, let `eta:A->E` be an embedding into an
AF algebra, and index matrices over `E` by `F`.  Define

```text
D(a)_(t,t)=eta(alpha_(t^-1)(a)),
U_s delta_t=delta_(s t).
```

The `U_s` are permutation unitaries in the multiplier algebra of
`M_|F|(E)`, and direct calculation gives

```text
U_s D(a) U_s* = D(alpha_s(a)).                       (1)
```

Although `U_s` need not belong to `M_|F|(E)` when `E` is nonunital, every
matrix `D(a)U_s` does.  Thus the integrated form of (1) defines

```text
rho:A rtimes_alpha F -> M_|F|(E),
rho(a u_s)=D(a)U_s.                                  (2)
```

It is injective.  Indeed, for an algebraic crossed-product element `x`, the
`t`th diagonal entry of `rho(x)` is

```text
eta(alpha_(t^-1)(E_A(x))).                           (3)
```

The same identity holds by continuity.  If `x>=0` and `rho(x)=0`, (3) and
injectivity of `eta` give `E_A(x)=0`.  The coefficient expectation is
faithful on the reduced crossed product.  Since `F` is finite, full and
reduced crossed products coincide, so `x=0`.  Finally `M_|F|(E)` is AF,
proving AF-embeddability.

Suppose additionally that `sigma eta=tau` and that `tau` is invariant.  If
`s` is nontrivial, left translation by `s` has no fixed point in `F`, so
`D(a)U_s` has zero diagonal.  For the identity coefficient,

```text
(tr_|F| tensor sigma)(D(a))
  = |F|^-1 sum_(t in F) tau(alpha_(t^-1)(a))
  = tau(a).
```

Therefore `(tr_|F| tensor sigma)rho=tau E_A`, proving the traced assertion.

For the commutative corollary, a second-countable locally compact `X` has a
compact metrizable one-point compactification.  A continuous surjection from
the Cantor set onto that compactification gives

```text
C_0(X) -> C(X union {infinity}) -> C(Cantor),
```

and `C(Cantor)` is AF.  Apply (2).

For the finite-index corollary, choose left-coset representatives
`Gamma=disjoint_union_(i=1)^n r_i Lambda`.  The decomposition

```text
l2(Gamma)=direct_sum_(i=1)^n l2(r_i Lambda)
```

turns the left regular representation of `Gamma` into matrices over
`C*_r(Lambda)`: if `g r_j=r_i h` with `h in Lambda`, the `(i,j)` entry is
the left regular unitary of `h`.  Hence

```text
C*_r(Gamma) -> M_n(C*_r(Lambda))
```

is injective.  Amenability identifies both reduced algebras with their full
group C*-algebras.  Matrix-amplifying an AF embedding of `C*(Lambda)` now
gives the asserted AF embedding of `C*(Gamma)`.
