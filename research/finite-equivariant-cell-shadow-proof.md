---
rg: 2
id: finite-equivariant-cell-shadow-proof
kind: route
title: Balance iid points in the translates of a fine fundamental-domain partition
target: finite-group-actions-have-coherent-same-cloud-shadows
requires:
  - hs-defect-is-mean-square-sphere-displacement
---

Let `S(H)` carry normalized spherical measure `mu`.

## Free conull part and equivariant cells

For `g!=h`, the coincidence set

```text
{x in S(H): V_g x=V_h x}
```

is the unit sphere of the fixed subspace of `V_(h^(-1)g)`.  Faithfulness
makes that subspace proper, so the coincidence set has spherical measure
zero.  Removing the finitely many such sets gives a conull Borel set
`X_free` on which `K` acts freely.

A finite Borel action on a standard Borel space has a Borel transversal:
for example, choose the least point in every orbit in a fixed Borel linear
order.  Let `D subset X_free` be such a transversal.  Since the sphere is
totally bounded, partition `D` into finitely many Borel sets

```text
D=C_1 disjoint_union ... disjoint_union C_L
```

of diameter strictly below `rho`.  The sets

```text
g C_l,              g in K, 1<=l<=L,                   (FGP1)
```

are pairwise disjoint, cover `X_free`, have diameter below `rho`, and
satisfy `mu(gC_l)=mu(C_l)`.

## Balance the sampled cells

Let `n_(g,l)` be the number of sampled cloud points in `gC_l`, and put

```text
m_l=min_(g in K) n_(g,l).
```

The strong law of large numbers, applied to the finite partition (FGP1),
gives

```text
n_(g,l)/N -> mu(C_l)
```

simultaneously for all `g,l`.  Hence

```text
N-|K| sum_l m_l=o(N).                                  (FGP2)
```

For each `g,l`, retain any `m_l` of the indices whose points lie in
`gC_l` and enumerate them as `i(g,l,a)`, `1<=a<=m_l`.  Define

```text
tau_s(i(g,l,a))=i(sg,l,a).                              (FGP3)
```

The retained set is invariant and (FGP3) is the disjoint union of exact
left-regular `K`-orbits.  On the discarded `o(N)` indices, let every
`tau_s` act trivially.  Thus `s |-> tau_s` is an exact action on all
`N` indices.

If `i=i(g,l,a)`, then `V_s x_i` and
`x_(tau_s(i))` both lie in `sgC_l`.  Their distance is therefore below
`rho`.  Equation (FGP2) proves (FGS1).  On every retained regular orbit,
`tau_g(i)!=tau_h(i)` for `g!=h`, giving the stated separation.

## Hilbert--Schmidt perturbations

Use the normalized Hilbert--Schmidt norm.  For a uniform spherical point
`x` and any operator `A`,

```text
E norm(Ax)^2=norm(A)_2^2.                               (FGP4)
```

Take `A=U_s-V_s`.  Markov's inequality gives

```text
mu{x:norm((U_s-V_s)x)>t} <= kappa_s^2/t^2.              (FGP5)
```

The empirical frequency of this event differs from its measure by `o(1)`
with probability tending to one; there are only finitely many labels.
Outside that event and the discarded set,

```text
norm(x_(tau_s(i))-U_s x_i)
 <= norm(x_(tau_s(i))-V_s x_i)
    +norm((V_s-U_s)x_i)
 < rho+t.
```

This proves (FGS2).

For a dimension-varying sequence, put

```text
kappa_n=max_(s in K) kappa_(s,n),       rho_n=1/n,
t_n=sqrt(kappa_n) if kappa_n>0, and t_n=1/n otherwise.
```

Then `rho_n,t_n->0` and

```text
max_s kappa_(s,n)^2/t_n^2 <= kappa_n -> 0.              (FGP6)
```

For the resulting finite equivariant partition in dimension `dim(H_n)`,
choose the cloud size `N_n` so large that, with probability at least
`1-1/n`, the balancing loss in `(FGP2)` is at most `N_n/n` and every
empirical perturbation frequency differs from its spherical measure by at
most `1/n`.  Such an `N_n` exists because the partition and the label set
are finite for each fixed `n`.  Choose one cloud on this event.  Equations
`(FGS2)` and `(FGP6)` now give shadow radius `rho_n+t_n->0` and
exceptional density at most `kappa_n+2/n->0`.  This is the required
dimension-varying diagonalization.

Finally, an exact regular-character representation of a finite group is
faithful: if `V_g=1` for `g!=e`, its normalized trace at `g` would be
one rather than zero.  Hence the theorem applies to the finite-group
regular-character tables used in the spherical program.  The construction
never invokes preselected matchings or gauge variables.
