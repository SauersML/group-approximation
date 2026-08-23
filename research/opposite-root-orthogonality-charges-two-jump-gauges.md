---
rg: 2
id: opposite-root-orthogonality-charges-two-jump-gauges
kind: claim
title: The involution row nonlinearly charges root-algebra phase plateaux in regular packets
distinct_from:
  two-jump-cycle-refutes-functional-calculus-gauge-bound: that shows the coboundary residual alone misses two phase plateaux; this proves the Weyl involution row detects them in a left regular arithmetic packet.
  iwahori-uniform-infinitesimal-rigidity: that is a linear Fox-Jacobian estimate for all congruence representations; this is an exact nonlinear one-row identity for root-algebra gauges in the regular representation.
  congruence-repair-bypasses-koopman-cycle-firewalls: that invokes the full mixed congruence repair theorem; this gives the elementary coercive mechanism for the concentrated two-jump firewall in regular quotient packets.
---

Let `Q` be a finite quotient of the arithmetic Iwahori presentation.  Let
`U=<u>` be the upper root subgroup, let `x` be the Weyl involution, and put
`L=x U x`.  Assume `U intersect L={1}`, as in `PSL_2(Z/n)` for odd `n`.
Work in the left regular representation with canonical trace `tau`.

For every unitary `c in C[U]`, perturb only the Weyl involution to `x'=c x`.
Then

```text
tau((x')^2)=tau(c x c x)=tau(c)^2,                     (ORO1)
||(x')^2-1||_2^2=2-2 Re(tau(c)^2).                    (ORO2)
```

Moreover

```text
min_(sigma in {+1,-1}) ||c-sigma||_2
 <= ||(c x)^2-1||_2.                                  (ORO3)
```

Thus the involution row gives a dimension-free, exact nonlinear bound on
the distance of the correcting root-algebra gauge from the only scalar
gauges which preserve involutivity.  For the half-cycle gauge in
`two-jump-cycle-refutes-functional-calculus-gauge-bound`, `tau(c)=0`, so

```text
||(c x)^2-1||_2=sqrt(2),                               (ORO4)
```

even though its BS coboundary residual is `sqrt(8/L)`.

The load-bearing hypothesis is the regular trace orthogonality of the two
opposite root algebras.  In an arbitrary modular-vertex representation the
mixed coefficient `tau(c x c x)` need not factor as `tau(c)^2`; and
canonical microstate convergence controls only each fixed word, while the
Fourier support of `c` moves with the root order.  Hence `(ORO1)` closes the
rank-concentrated firewall on exact regular congruence packets but does not
by itself prove the noncongruence/relative-exactification theorem.

