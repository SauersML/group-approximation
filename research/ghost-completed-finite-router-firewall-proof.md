---
rg: 2
id: ghost-completed-finite-router-firewall-proof
kind: route
title: Induce the ghost character, then test the only possible common corner
target: ghost-finite-router-induced-sector-or-perfect-corner
requires: []
---

Realize `Ind_A^K(chi_g)` on the usual equivariant function space.  By
Frobenius reciprocity,

```text
Hom_A(chi_g, Res_A^K Ind_A^K(chi_g)) != 0.              (GFP1)
```

Equivalently, the spectral projection of the commuting selector subgroup is
nonzero:

```text
pi_g(e_g)!=0.                                          (GFP2)
```

This is an exact representation of the whole finite group `K`.  Every word
which is the identity in `K`, every entry of its multiplication table, and
every finite group-algebra identity therefore holds exactly under `pi_g`.
The normalized trace of `pi_g(e_g)` is positive, while the right side of
`(GFR4)` is zero.  This proves the first assertion.  Adding a finite label
group or controlled routing permutations merely replaces `K` by another
finite group containing the same selector subgroup, so the identical
induction argument applies.

For the corner assertion, put

```text
p_(c,t)=q e_(c,t)=e_(c,t)q.                            (GFP3)
```

These are orthogonal projections in the finite-dimensional algebra
`q C[K]q` and

```text
sum_t p_(c,t)=q,                 p_(c,g)=0.             (GFP4)
```

Thus the nonzero atoms in context `c` are supported on `R_*`.  The decoded
coordinate signs are

```text
X_(c,i)=sum_t (-1)^(t_i) p_(c,t).                      (GFP5)
```

They are commuting involutions with corner unit `q`.  By hypothesis the
sign attached to an occurrence of a shared variable is independent of the
context, so `(GFP5)` is one globally compatible family.  The normalized
restriction of the finite canonical trace,

```text
tau_q(x)=tau_K(x)/tau_K(q),                             (GFP6)
```

therefore gives a finite-dimensional perfect tracial strategy.  This
contradicts any strict finite-dimensional soundness gap and proves the
second assertion.

The two halves are exhaustive for a finite router used in this manner.  If
no corner removes the induced ghost sectors, they are exact local
countermodels.  If one common commuting corner removes them and synchronizes
the coordinates, that corner is already the forbidden finite perfect model.
