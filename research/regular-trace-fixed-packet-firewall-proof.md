---
rg: 2
id: regular-trace-fixed-packet-firewall-proof
kind: route
title: Restrict the regular trace to the finite packet and compare Murray-von Neumann ranks
target: regular-trace-forbids-fixed-finite-packet-rank-return
requires: []
---

Let `lambda_Gamma` be the left regular representation and put

```text
tau_reg(a)=<lambda_Gamma(a) delta_e,delta_e>.
```

This is a tracial state on `C^*_max(Gamma)`, through the quotient onto the
reduced group C-star algebra.  For a finite subgroup `F <= Gamma`, the
restriction of `lambda_Gamma` to `F` is a direct sum of copies of the regular
representation of `F`, indexed by the left `F`-orbits in `Gamma`.  Hence the
restriction of `tau_reg` to `C[F]` is the canonical coefficient-at-the-identity
trace.  Since

```text
C^*(F)=C^*_r(F)
```

is finite dimensional and the regular representation is faithful, this trace
is faithful.  In particular every nonzero projection in `C[F]` has strictly
positive `tau_reg`-value.

If `u` is a unitary and `u e u^*=f`, traciality gives

```text
tau_reg(e)=tau_reg(u e u^*)=tau_reg(f).                 (RPF1)
```

Thus projections with unequal regular traces cannot be unitarily equivalent,
even in the whole full group C-star algebra.  If `e,f in C[F]`, `f<=e`, and
`u e u^*=f`, then `(RPF1)` gives

```text
tau_reg(e-f)=0.
```

The difference is a positive element of `C[F]`; faithfulness of the restricted
trace gives `e-f=0`, so `e=f`.

Finally suppose that a nonzero `e in C[F]` were properly infinite in
`C^*_max(Gamma)`.  There would be orthogonal projections `e_1,e_2<=e`, each
Murray-von Neumann equivalent to `e`.  Traciality and positivity would give

```text
tau_reg(e)
 >= tau_reg(e_1)+tau_reg(e_2)
 = 2 tau_reg(e),
```

so `tau_reg(e)=0`, contradicting faithfulness on `C[F]`.

Therefore a fixed finite-packet carrier cannot itself support the unequal-rank
return needed for a direct-finiteness contradiction.  Representation-dependent
spectral cuts evade the argument because their regular trace is not fixed by
the abstract group algebra; a Kazhdan projection evades it because its regular
image is zero.  Those are precisely the two mouths left open by the theorem.
