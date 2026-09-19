---
rg: 2
id: norm-ultraproduct-saturation-does-not-decode-corona-root-germs
kind: claim
title: Countable saturation cannot create Leavitt arrows from finite root multiplicity germs
distinct_from:
  finite-root-windows-share-one-reducing-corona-carrier: that places every finite root window on one nonzero corona projection; this proves that the resulting operator type is not finitely satisfiable even after that projection is sent to a countably saturated norm ultraproduct.
  atomic-leavitt-gap-on-nonzero-matrix-corner: that gives the terminal dimension-free gap once coefficient operators have been returned; this identifies the exact finite-satisfiability failure which prevents saturation from returning them.
artifacts:
  - research/norm-ultraproduct-saturation-finite-type-fence-proof.md
---

**ESTABLISHED SATURATION FENCE.** Let

```text
Q_d=(product_n M_(d_n)(C))/(direct-sum_n M_(d_n)(C))
```

and let `P!=0` be the common reducing corona projection supplied by
`finite-root-windows-share-one-reducing-corona-carrier`.  Choose a free
ultrafilter `U` containing the infinite support of a projection lift of `P`,
and let

```text
A_U=product_U M_(d_n)(C),             p=image_U(P).
```

Then `p!=0`.  Even granting countable saturation of the corner `p A_U p`,
the finite additive/Heisenberg multiplicity data do **not** make the
binary-Leavitt coefficient type finitely satisfiable there.

Indeed, fix `K>=1`.  In the `K`-balls of `p A_U p`, the finite fragment

```text
T_0 S_0=p,             T_1 S_1=p,             T_0 S_1=0              (NSF1)
```

already has a positive operator-norm gap.  More precisely, if all four
variables have norm at most `K` and the first two residuals are at most
`epsilon<1`, then

```text
||T_0 S_1|| >= (1-epsilon)^2/K^2.                              (NSF2)
```

Consequently `(NSF1)` cannot have all three residuals below `epsilon` when

```text
epsilon < min(1/2,1/(4K^2)).                                  (NSF3)
```

The alternative finite fragment

```text
T_i S_i=p  (i=0,1),             S_0T_0+S_1T_1=p               (NSF4)
```

has the norm-bound-independent `1/3` gap of
`atomic-leavitt-gap-on-nonzero-matrix-corner`.

Finite-root Heisenberg windows supply root unitaries, Fourier/isotypic
projections and their rank-germ branching identities.  They supply no
operators `S_i,T_i` witnessing either `(NSF1)` or `(NSF4)`, and in fact those
finite fragments are precisely what no nonzero norm-matrix-ultraproduct
corner can approximately realize.  Countable saturation realizes only a
countable bounded type whose every finite fragment is already approximately
satisfiable in this one corner; it does not turn compatible ranks into new
intertwiners.

Thus passage to a support ultrafilter does not close
`corona-coefficient-module-decoder`.  A successful route must first prove a
genuine mixed/opposite-root return theorem producing finite-window
coefficient-operator witnesses with fixed norm bounds.  Once that finite
fragment is produced, the Atomic Leavitt Gap already gives the contradiction
and saturation is unnecessary.

