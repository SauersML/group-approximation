---
rg: 2
id: relative-leavitt-active-subspaces-expand-by-two
kind: claim
title: Every finite active coefficient subspace has a full-sized binary Leavitt boundary
distinct_from:
  approximate-relative-leavitt-cell-kills-active-trace: that is a normalized-Hilbert--Schmidt trace inequality for already decoded contractions; this is the exact algebraic expansion statement that a root-character decoder must turn into such contractions.
  affine-active-corner-has-faithful-binary-leavitt-envelope: that identifies the whole active module with two copies of itself; this gives the sharp finite-subspace boundary inequality used by finite-window arguments.
  free-root-top-boundary-reservoir-is-summable: that telescopes character mass across a polynomial-degree filtration; this is coefficient-space expansion inside one relative Leavitt cell and uses no Fourier filtration.
---

Let `R=L_A(S)` be a relative binary Leavitt envelope and let `V` be a
finite-dimensional `k`-subspace of the active left ideal `AR`.  Then

```text
Phi_V:V direct_sum V -> AR,
Phi_V(v_0,v_1)=s_0v_0+s_1v_1                         (LAS1)
```

is injective.  Consequently

```text
dim_k(s_0V+s_1V)=2 dim_k(V).                           (LAS2)
```

In particular, if a finite-dimensional subspace `W subset AR` contains
`V+s_0V+s_1V`, then

```text
dim_k(W)>=2 dim_k(V).                                  (LAS3)
```

Thus no nonzero finite active coefficient window is invariant under both
left branch maps.  More quantitatively, any nested finite-window construction
which contains its previous window has boundary dimension at least the full
dimension of that previous window at every completed binary step.

The constant is sharp: equality in `(LAS3)` occurs when
`W=s_0V direct_sum s_1V` and `V` is already contained in this sum.

This is the coefficient-side expansion which the affine Steinberg decoder
needs to see.  It does not itself control a normalized-HS group microstate:
the root representation records additive characters, and a character may be
nontrivial on many linearly independent boundary coefficients at once.  A
successful decoder must therefore charge the boundary through the paired
Steinberg multiplication shears, not merely count coefficient vectors.
