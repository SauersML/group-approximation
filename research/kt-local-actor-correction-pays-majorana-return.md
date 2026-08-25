---
rg: 2
id: kt-local-actor-correction-pays-majorana-return
kind: claim
title: Correction only on the Kazhdan packet and mixed return pays the full Majorana defect
distinct_from:
  kt-full-kazhdan-majorana-return-collapses-in-fd: that proves the zero-correction genuine-actor inequality; this quantifies the perturbation cost and shows that correction is needed only on the finite set K union {h}.
  kt-wreath-relative-canonical-actor-exactification: that asks for correction of a fixed actor generating set after negligible padding; this records the strictly local terminal estimate once a genuine full-actor representation is close only on K union {h}.
  el-r-polynomial-robust-spectral-gap: that controls the low spectrum of an approximate Gamma adjoint Laplacian but does not construct a genuine full-actor representation; this makes the missing presentation-to-representation modulus explicit rather than assuming it.
---

**ESTABLISHED.**  Use the packet `K`, mixed return `h`, and Kazhdan
constant `kappa_K` of
`kt-full-kazhdan-majorana-return-collapses-in-fd`.  Let `(u_s)_(s in K)`
and `u_h` be unitary matrices.  Suppose there is a genuine representation
`rho:G->U(D)` on the same space such that

```text
epsilon=max({||u_s-rho(s)||_2:s in K} union {||u_h-rho(h)||_2}). (LAC1)
```

For every self-adjoint involution `c`, put

```text
d=u_h c u_h^*,
delta_K=max_(s in K)||[c,u_s]||_2.
```

Then

```text
||cd+dc||_2
 >= 2-(4/kappa_K)delta_K-(8/kappa_K+4)epsilon.             (LAC2)
```

Thus no correction of the lamp or of the entire actor table is needed for
the terminal contradiction.  It is enough to correct the actor on the
single finite interface `K union {h}` to a representation of the **full**
actor.

In particular, if a source-specific theorem supplies a finite window `F`
and a modulus `eta(t)->0` such that every relevant normalized-HS actor
microstate `u` has a genuine full-actor representation satisfying

```text
epsilon <= eta(def_F(u)),                                  (LAC3)
```

then `(LAC2)` is the requested dimension-free robust Majorana floor.  The
term `(LAC3)` is a real presentation-to-representation exactification
hypothesis; neither property `(T)`, `(T;FD)_rob`, nor finite-dimensional
compression invisibility proves it.  For rank `r=3` it must be formulated
with a finite multiplication window because the polynomial elementary group
is not finitely presented.  A fixed finite-relator formulation must instead
pin a rank where the actor presentation is known finite (for this programme,
`r>=5`).

DERIVATION
kt-local-actor-correction-majorana-proof
