---
rg: 2
id: agent-free-compressor-kernel-multiplicity-firewall-proof
kind: route
title: Tensor the quotient packet with finite regular representations separating one kernel word
target: agent-free-compressor-kernel-multiplicity-firewall
requires: []
---

The covariance relation in `(FKM1)` is preserved by `(FKM2)`, since

```text
rho(f)rho(d)rho(f)^(-1)
 =pi(theta(f)d theta(f)^(-1)) tensor 1
 =rho(beta(theta(f))(d)).                              (FKP1)
```

All remaining defining relations are immediate, so `rho` is exact.

Fix `1!=k in ker(theta)`.  The free group is torsion-free and residually
finite.  The orders of the image of `k` in finite quotients are therefore
unbounded: if they were bounded by `m`, then `k^(lcm(1,...,m))` would vanish
in every finite quotient, contradicting residual finiteness.  Choose a finite
quotient

```text
q:F->Q
```

such that the order `ell` of `q(k)` is at least `M`, and take `kappa=lambda_Q`,
the left regular representation.

The permutation `lambda_Q(q(k))` consists of `|Q|/ell` cycles of length
`ell`.  Hence each of its `ell` eigenvalues has multiplicity `|Q|/ell`, and

```text
dim Fix(Ad lambda_Q(q(k)))
 =ell (|Q|/ell)^2
 =|Q|^2/ell.                                          (FKP2)
```

For `k in ker(theta)`, `(FKM2)` gives

```text
rho(k)=1 tensor lambda_Q(q(k)).                        (FKP3)
```

The packet projection is `pi(p) tensor 1`, so its full adjoint corner is

```text
End(pi(p)H_pi) tensor End(ell^2(Q)).                  (FKP4)
```

Equations `(FKP2)--(FKP4)` show that the fraction of `(FKP4)` fixed by
`Ad rho(k)` is `1/ell<=1/M`.  On the other hand, dividing the dimension of
`(FKP4)` by `(dim H_pi |Q|)^2` gives exactly `(FKM4)`.  Thus the packet
carrier remains macroscopic while its free-kernel-fixed part can be made
arbitrarily sparse, completing the firewall.
