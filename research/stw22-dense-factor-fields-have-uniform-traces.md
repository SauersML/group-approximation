---
rg: 2
id: stw22-dense-factor-fields-have-uniform-traces
kind: claim
title: Asymptotically dense unique-trace fibres have only uniform traces over finite Bratteli patterns
distinct_from:
  stw22-finite-bratteli-cubes-have-only-uniform-traces: that theorem requires every finite-coordinate building block to be a full matrix algebra; the present theorem permits arbitrary nuclear unique-trace subalgebras whose GNS closures may already be hyperfinite II_1 factors, without nesting or finite dimensionality.
  stw22-derived-set-gap-trace-reduction: that theorem treats one constant UHF field; the present theorem treats changing factor subfields and obtains derived-set extension from asymptotically identity conditional expectations.
artifacts:
  - research/artifacts/stw22-asymptotically-dense-factor-field-audit-2026-08-30.md
---

Fix `d>=1`.  For `1<=i<=d`, let `U_i` be an infinite-dimensional UHF
algebra with unique trace `tau_i`.  For every `n>=1`, let

```text
D_(i,n) subset U_i
```

be a unital nuclear C*-subalgebra with a unique tracial state.  Assume only
the asymptotic density condition

```text
dist(u,D_(i,n)) -> 0       for every u in U_i.           (ADF)
```

The algebras `D_(i,n)` need not be finite dimensional or nested.  Put

```text
X_i={infinity,1,2,...},
B_i={ (a_infinity,a_1,a_2,...):
        a_infinity in U_i, a_n in D_(i,n),
        ||a_n-a_infinity|| -> 0 }.
```

Let `X=product_i X_i`, `B=tensor_i B_i`, let `K` be any nonempty closed
subset of `X`, and define the central restriction

```text
B_K=B/closure(C_0(X\K)B).
```

Then `B_K` is separable, unital, and nuclear, its extreme trace boundary is
canonically `K`, and every trace on its uniform tracial completion is
uniformly `2`-norm continuous.

More precisely, write `R_i=pi_(tau_i)(U_i)''`,

```text
N_(i,n)=pi_(tau_i)(D_(i,n))'' subset R_i,
N_(i,infinity)=R_i,
R=bar-tensor_i R_i,       N_x=bar-tensor_i N_(i,x_i).
```

Every `N_x` is a finite factor, and the uniform completion is

```text
M_K={a:K -> R: sup_x ||a(x)||<infinity,
                  a(x) in N_x,
                  x |-> a(x) is ||.||_2-continuous}.
```

Every tracial state on `M_K` is uniquely

```text
a |-> integral_K tau_x(a(x)) dmu(x)
```

for a probability measure `mu` on `K`.

This class strictly contains the finite Bratteli-cube class.  For example,
write `U=bigotimes_(j>=1) M_2` and let `D_n` be the unital tensor subalgebra
supported on

```text
{1,...,n} union {n+2,n+4,n+6,...}.
```

Each `D_n` is an infinite-dimensional UHF algebra, `(ADF)` holds because
`D_n` contains the first `n` tensor factors, and `D_n''` is a proper
hyperfinite `II_1` subfactor of `R` with a nontrivial relative commutant.
Thus even the isolated fibres may all be `II_1` factors rather than matrix
factors.  Finite products and closed restrictions of these sequences give
tree-shaped changing-factor fields of every finite Cantor--Bendixson
height.
