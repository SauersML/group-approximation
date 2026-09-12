---
rg: 2
id: fournier-facio-invariant-mass-growth-proof
kind: route
title: Covariance of the commutant expectation plus orthogonality of an infinite conjugacy orbit
target: fournier-facio-invariant-mass-grows-along-compressor
requires:
  - fournier-facio-group-contains-simple-wreath-shift
---

**Monotone.**  Write `v = u(t_1)`.  Since `t_1 Gamma t_1^-1 <= Gamma`,
`vAv^* = u(t_1 Gamma t_1^-1)' cap M` contains `A`.  Covariance of trace-preserving
conditional expectations gives `E_A(v^* x v) = v^* E_(vAv^*)(x) v`, hence

```text
F(theta(x)) = ||E_(vAv^*)(x)||_2^2 >= ||E_A(x)||_2^2 = F(x),
```

because `L^2(A) <= L^2(vAv^*)`.

**Jump.**  The conjugation action of `Gamma` on `L^2(M)` is a unitary
representation.  Its invariant vectors are `L^2(A)`: the minimal-norm point of
the closed convex hull of a bounded orbit lies in `M`.  So `E_A(x)` is the
minimal-norm point of the closed convex hull of `{u(gamma) x u(gamma)^*}`.

For `g in pi(S)\{1}` this orbit consists of the `u(h)` with `h` in the
`Gamma`-conjugacy class of `g`.  That class is infinite, since it contains the
`pi(S)`-class of `g`, and a nontrivial element of an infinite simple group has
an infinite class.  The regular character makes the vectors `u(h)` pairwise
orthogonal of norm one, and averages of `n` of them have norm `n^(-1/2)`.
Hence `E_A(u(g)) = 0`.

On the other side, `theta(u(g)) = u(t_1^-1 g t_1) in u(J_0)`, and `J_0`
centralizes `Gamma` by clause (W3).  So `theta(u(g)) in A` and
`F(theta(u(g))) = ||u(t_1^-1 g t_1)||_2^2 = 1`.
