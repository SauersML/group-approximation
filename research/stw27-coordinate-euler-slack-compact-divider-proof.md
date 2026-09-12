---
rg: 2
id: stw27-coordinate-euler-slack-compact-divider-proof
kind: route
title: Reduce the complement modulo a prime and lift projection comparison through the diagonal limit
target: stw27-coordinate-euler-slack-obstructs-compact-dividers
requires:
  - stably-finite-compact-cu-elements-are-projections
  - projection-comparison-lifts-through-injective-limits
artifacts:
  - research/artifacts/stw27-villadsen-compact-divider-no-go-audit-2026-08-30.md
---

Work first over `Z=(S^2)^N`.  Let `e_i in H^2(Z;F_ell)` be the generator
from the `i`-th sphere.  The cohomology ring is

```text
H^*(Z;F_ell)=F_ell[e_1,...,e_N]/(e_1^2,...,e_N^2).
```

Suppose `ell F` is a subbundle of `E`, and write

```text
E isomorphic to ell F direct_sum G.
```

In mod-`ell` cohomology, Frobenius and the square-zero relations give

```text
c(F)^ell=1.
```

Indeed every positive-degree monomial is square-free, so its `ell`-th
power vanishes.  Hence

```text
c(E)=c(G)  in H^*(Z;F_ell).                            (1)
```

On the other hand,

```text
c(E)=product_i (1+e_i)^(t_i)
    =product_i (1+(t_i mod ell)e_i).
```

The component in degree `2N_ell` contains the nonzero monomial

```text
product_(ell does not divide t_i) e_i
```

with nonzero coefficient.  Therefore `(1)` forces
`c_(N_ell)(G) != 0`, and thus

```text
rank(G) >= N_ell.                                     (2)
```

Put `r=rank(F)`.  The second assumed subbundle relation gives
`M <= (ell+1)r`, while the first gives

```text
rank(G)=M-ell r <= M/(ell+1).                         (3)
```

Combining `(2)` and `(3)` proves `(V)`.

Now consider the diagonal inductive limit.  The image of the seed Hopf
projection at stage `j` is the bundle

```text
theta_(s_j) direct_sum direct_sum_k L_k^(direct_sum t_(k,j));
```

point-evaluation eigenmaps contribute the trivial summands.  Suppose a
compact `y in Cu(A)` satisfied `(C)`. The limit is stably finite, so the
compact-class theorem represents `y` by a projection in `A tensor K`.
Continuity of the Murray--von Neumann semigroup for injective inductive
limits represents that projection at some stage and lifts both comparison
inequalities simultaneously to a later stage. At every sufficiently late
stage this contradicts `(V)`.
Therefore no compact divider exists.
