---
rg: 2
id: twisted-group-basis-forces-affine-context-support-proof
kind: route
title: Fourier transform the scalar kernel of the commuting involution subgroup
target: twisted-group-basis-forces-affine-context-support
requires: []
---

Because the `x_i` commute and square to one, `X:F_2^k->U(M)` is an honest
homomorphism. Projective basis closure gives a homomorphism from `F_2^k` to
the basis-index group. Its kernel `K` consists exactly of scalar products.
On `K`, those scalars form a character `chi:K->{+1,-1}`; choose `a_0` with
`chi(s)=(-1)^(a_0 dot s)`.

The joint atom is

```text
p_a=2^(-k) sum_s (-1)^(a dot s) X(s).
```

Canonical trace kills every nonscalar basis line, so

```text
tau(p_a)=2^(-k) sum_(s in K) (-1)^((a+a_0) dot s).
```

Fourier orthogonality makes this `|K|/2^k` precisely on
`a_0+K^perp` and zero off it. Since the trace is faithful, zero trace for the
positive projection `p_a` means `p_a=0`; hence the support statement is exact.
