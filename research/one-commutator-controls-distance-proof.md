---
rg: 2
id: one-commutator-controls-distance-proof
kind: route
title: The Poincare form of the lazy average plus the shared h-displacement of all coset words
target: one-commutator-controls-distance-to-full-commutant
requires:
  - hecke-averaging-realizes-commutant-expectation
---

**The machinery applies to vectors.**  The proof of
`hecke-averaging-realizes-commutant-expectation` used unitarity of
`k` only to normalize; for any exactly `Lambda`-central vector
`xi in L^2(M)` the coefficient `g -> <Ad pi(g) xi, xi>` is positive
definite (Gram), `Lambda`-bi-invariant with constant value
`||xi||^2` on `Lambda`, and extends to the completion; the closed
`Ad pi(Gamma)`-cyclic subspace `V` of `xi` carries the
`G`-representation `rho`, `xi` is `K`-fixed, and `xi = xi_0 + xi_1`
with `xi_0 = E(xi)` and `xi_1 in V_1^K`, exactly as there.  On
`V_1^K` the lazy operator `S` is self-adjoint with numerical range in
`[0, 1 - delta_0]`.

**Poincare inequality.**  Since `S xi_0 = xi_0` and `S` preserves
`V_1`,

```text
Re <(1 - S) xi, xi> = Re <(1 - S) xi_1, xi_1> >= delta_0 ||xi_1||^2.
```

On the other hand, expanding `S = (1/2) + (1/(2L)) sum_i Ad pi(w_i)`
and using `||Ad pi(w_i) xi|| = ||xi||`,

```text
Re <(1 - S) xi, xi>
  = (1/(2L)) sum_i ( ||xi||^2 - Re <Ad pi(w_i) xi, xi> )
  = (1/(4L)) sum_i || Ad pi(w_i) xi - xi ||^2.
```

**All coset words share one displacement.**  The representatives can
be taken as `w_i = u_i h` with `u_i in Lambda`
(`Lambda h Lambda = sqcup u_i h Lambda`; the explicit `u_i` are the
words enumerated by `experiments/hecke42_average_probe.py` at
`(n, p) = (3, 2)`).  Since `xi` is exactly `Lambda`-central and
`Ad pi(u_i)` is unitary,

```text
|| Ad pi(w_i) xi - xi || = || Ad pi(u_i)( Ad pi(h) xi - xi ) ||
                        = || Ad pi(h) xi - xi ||
```

for every `i`.  Hence `(1/(4L)) sum_i ||...||^2 =
(1/4) || Ad pi(h) xi - xi ||^2`, and combining with the Poincare
inequality gives

```text
(1/4) || Ad pi(h) xi - xi ||^2 >= delta_0 || xi - E(xi) ||^2,
```

which is `(OC1)`.  For a unitary `k`, `Ad pi(h) k - k =
pi(h) k pi(h)^* - k` has the same `2`-norm as `[k, pi(h)]`, and
`|| k - E(k) ||_2 = dist_2(k, pi(Gamma)' cap M)` because `E` is the
orthogonal projection onto that subspace.
