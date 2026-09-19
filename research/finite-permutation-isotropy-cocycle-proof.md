---
rg: 2
id: finite-permutation-isotropy-cocycle-proof
kind: route
title: Use positivity and finite-dimensional orthogonality on stabilizer fibers
target: finite-permutation-cocycles-cannot-cancel-infinite-isotropy
requires:
  - manzoor-isotropy-has-no-positive-finite-type-corner
---

For a permutation cocycle, the fixed-point trace formula is

```text
(tr_n tensor tau_R)(v_g)
 =integral_(Fix(g)) |Fix(sigma_g(x))|/n dmu(x).          (FPP1)
```

The integrand is nonnegative. If the left side vanished for every `g!=e`,
then for each such `g`, `sigma_g(x)` would have no fixed point for almost
every `x in Fix(g)`. Since `Gamma` is countable, discard one null set
simultaneously for all `g`.

Fix a remaining `x` and put `H=Gamma_x`. On `H`, the cocycle identity
becomes

```text
sigma_(hk)(x)=sigma_h(x)sigma_k(x),                     (FPP2)
```

because every element of `H` fixes `x`. Thus `h |-> sigma_h(x)` is a
permutation action of `H` on `{1,...,n}`. Every `h!=e` is fixed-point-free
by `(FPP1)`. The action is therefore free: each orbit has cardinality
`|H|`, so `H` is finite and `|H|<=n`. This contradicts the assumed
infinite stabilizer and proves `(FPC2)`.

For the unitary strengthening, `(FPC3)` again makes
`h |-> b_h(x)` a representation of `H`. Distinct elements give orthogonal
matrices in the normalized Hilbert--Schmidt inner product:

```text
tr_n(b_h(x)^*b_k(x))
 =tr_n(b_(h^(-1)k)(x))
 =1_(h=k).                                              (FPP3)
```

The vector space `M_n(C)` has dimension `n^2`, so it contains at most
`n^2` mutually orthogonal nonzero vectors. Hence `|H|<=n^2`, proving the
general statement.

The positivity in `(FPP1)` is load-bearing. A scalar or monomial cocycle may
have complex fixed-set integrands whose averages cancel even when no fiber
character is regular. Such diffuse cross-base cancellation is exactly the
residual gate, not a loophole in the argument.
