---
rg: 2
id: finite-shell-window-cannot-wordize-returning-tag
kind: claim
title: No fixed finite shell window wordizes a returning injective phase tag
distinct_from:
  actor-algebra-cannot-wordize-shell-phase-tag: that gives the constant-line obstruction on one transitive 42-point shell; this treats arbitrary finite unions of shell orbits and the diagonal crossed-product alternative.
  shortest-second-denominator-return-has-coweight-holonomy: that computes the alternative-return word `k=diag(2,2,1/4)` and exhibits Folner cuts with asymptotically small boundary; this proves every fixed finite window has a positive boundary and hence cannot make that return into a fixed relator-controlled tag.
  every-fixed-hecke-window-retains-graph-product-nonedges: that blocks Boolean completion through native lamp cliques; this blocks an injective phase coefficient even if a full diagonal coefficient algebra is granted on the window.
---

Let a group `G` act on a finite disjoint union of transitive sets

```text
Omega=disjoint_union_(r=1)^s Omega_r,       |Omega|=Q, (FSW1)
```

and let `rho` be the permutation representation. For a diagonal unitary

```text
A=sum_(x in Omega) alpha_x P_x,             |alpha_x|=1, (FSW2)
```

put `bar_alpha_r=|Omega_r|^(-1)sum_(x in Omega_r)alpha_x`. Then every
operator `X` in the actor group algebra satisfies

```text
||A-X||_2^2
 >=(2/Q)sum_(r=1)^s(1-|bar_alpha_r|^2).                (FSW3)
```

Thus enlarging the native 42-point chart to any fixed finite union of
`SL_3(Z)`-shells does not remove the actor-algebra obstruction. If one shell
is tagged by all `42`nd roots, it contributes `2/Q`; on a two-shell window
`Q=84` this is at least `1/42`. If both shells carry full root sets, the
floor is `1/21`.

Now grant the entire diagonal coefficient algebra, so the tag `(FSW2)`
itself is available. The shortest nonbacktracking second-denominator return
from `shortest-second-denominator-return-has-coweight-holonomy` acts by

```text
k=diag(2,2,1/4).                                       (FSW4)
```

Its action on

```text
X=SL_3(Z[1/2])/SL_3(Z)                                 (FSW5)
```

has no finite orbit. Hence no nonempty finite coefficient window `F subset X`
is `k`-invariant. If `A_F` is any diagonal partial phase tag supported on
`F`, with every nonzero coefficient of modulus one, then on the finite
coordinate space indexed by `F union kF`, normalized Hilbert--Schmidt norm
gives

```text
||k A_F k^(-1)-A_F||_2^2
 >=|F triangle kF|/|F union kF|
 >=1/|F|.                                              (FSW6)
```

In particular every fixed two-shell or other fixed-window coefficient pays
a positive return-covariance floor. This floor is not a native relator
defect: `k` is a genuine nonidentity coweight word, and exact
representations satisfy all arithmetic relators while moving the window.

Consequently the minimal two-cycle-to-four-cycle Morita lift, its shortest
A2 path, and one second denominator do not yield a fixed finite-window
injective tag whose covariance is bounded by presentation defect. The only
diagonal-coefficient escape is a sequence of windows with size tending to
infinity and boundary tending to zero, exactly the affine-Weyl Folner branch
already isolated in the arithmetic decoder. Closing that branch requires a
nonamenable off-shell incidence, not a larger fixed window.
