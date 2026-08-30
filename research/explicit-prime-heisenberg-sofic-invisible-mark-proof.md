---
rg: 2
id: explicit-prime-heisenberg-sofic-invisible-mark-proof
kind: route
title: Amalgamate one Bernoulli lamp with a Heisenberg generator and conjugate all nonzero lamps by finitary transvections
target: explicit-prime-heisenberg-sofic-invisible-mark
requires:
  - prime-heisenberg-compressor-hyperfinite-invisibility
artifacts:
  - research/artifacts/prime-heisenberg-sofic-invisibility-2026-08-30.md
---

Fix `F=F(a,b)` and let

```text
N=direct_sum_(g in F) F_p delta_g.                            (EPH2)
```

The left shift of `F` acts on `N`.  Let `L=E_fin(N)` be the group generated
by the elementary transvections of the countable vector space `N`, each of
which is the identity off a finite-dimensional coordinate subspace.  Shifts
normalize `L`; put

```text
K=L semidirect F,              G=N semidirect K.               (EPH3)
```

The group `G` is finitely generated.  Indeed, conjugating the four adjacent
transvections

```text
E_(e,a), E_(e,a^-1), E_(e,b), E_(e,b^-1)
```

by `F` gives every directed Cayley-edge transvection.  The identity
`[E_(i,j),E_(j,k)]=E_(i,k)` along reduced paths gives every elementary
transvection.  Hence these four elements and `a,b` generate `K`.  The
`L`-orbit of `delta_e` is all of `N\{0}` (finite-dimensional special linear
groups are transitive on nonzero vectors), so adjoining `delta_e` generates
`G`.

We also need the approximation class of `G`, and record it directly rather
than invoking the false generic implication amenable-by-sofic implies sofic.
The group `G` is LEF.  Given a finite multiplication packet, collect the
finite set of indices in `F` touched by its lamp vectors, finitary matrices,
and all translates occurring in the products.  Residual finiteness of the
free group gives a finite quotient `F->Q` injective on that set and on all
the finitely many required differences.  Send the collected lamp vectors
to `F_p^Q`, the finitary matrices to the corresponding matrices on
`F_p^Q`, and shifts to `Q`.  No relevant coordinates collide, so every
specified product is preserved inside the finite affine group

```text
F_p^Q semidirect (GL(F_p^Q) semidirect Q).
```

Now let

```text
H_p=<x,y,w | x^p=y^p=w^p=1, w central, [x,y]=w>
```

be the order-`p^3` Heisenberg group (for `p=2`, this is the corresponding
extraspecial group).  In `G times <w>` take
`C=<delta_e,w> ~= C_p^2`, and in `H_p` take `C'=<y,w>`.  Define

```text
Gamma_p=(G times <w>) *_(delta_e=y, w=w) H_p.                  (EPH4)
```

Both vertex groups inject into the amalgam, so `w` remains nontrivial of
order `p`.  It is central because it is central in both vertex groups.
The preceding finite generating set for `G`, together with `x`, generates
`Gamma_p`.  The first vertex group is LEF and hence sofic, the other is
finite, and amalgamated free products of sofic groups over finite (indeed
amenable) subgroups are sofic.  Thus `Gamma_p` is sofic.

It remains to apply the hyperfinite obstruction.  Inside `Gamma_p` use the
subgroup

```text
B=N semidirect F.                                             (EPH5)
```

The actor `F` is nonamenable.  On
`N_hat=(F_p)^F`, every nonidentity shift has Haar-null fixed set: its left
translation orbits are infinite cosets of an infinite cyclic subgroup, and
a Haar-random configuration is constant on such an orbit with probability
zero.

Take the compressor family `V={y}`.  Every nonzero `n in N` is conjugate to
`delta_e=y` by `L`.  With Weyl words `d_(u,v)=x^u y^v`, conjugation by `y`
is

```text
y d_(u,v) y^(-1)=w^(-u)d_(u,v).                              (EPH6)
```

Thus its symplectic linear part is the identity and its phase on the fixed
space `F_p^2` is the nonzero functional `(u,v)|->-u`.  All hypotheses of
`prime-heisenberg-compressor-hyperfinite-invisibility` hold, so every
finite injective representation kills `w`.

Soficity gives a faithful embedding of `Gamma_p` into a tracial matrix
ultraproduct and hence into `U(R^omega)`.  An embedding into `U(R)` would be
a finite injective representation retaining the nontrivial element `w`,
contradicting the preceding paragraph.  This proves `(EPH1)`.
