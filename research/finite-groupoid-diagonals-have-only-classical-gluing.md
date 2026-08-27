---
rg: 2
id: finite-groupoid-diagonals-have-only-classical-gluing
kind: claim
title: Finite groupoid object diagonals glue a BCS only through its classical limit
distinct_from:
  inverse-semigroup-globalization-cannot-groupify-nonru-bcs: that proves all support idempotents in one inverse semigroup commute and audits full-group trace; this computes the strict limit of a diagram of coarse diagonal inclusions and the effect of passing to one connected object corner.
  finite-sheet-transport-networks-are-exactly-matricial: that builds an exact monomial model when edge data are retained as covariances; this proves why replacing those transports by literal shared-marginal equalities is exactly a common classical refinement.
  common-corner-literal-contexts-stop-at-bass-serre: that allows arbitrary literal corner elements and excludes every finite graph of finite groups by CE permanence; this first shows that native groupoid object projections disappear or become one common diagonal under the proposed Morita corner.
---

Let a finite BCS have context answer sets `R_c`.  The context diagonal is
`D_c=C^(R_c)`, and the inclusion of a shared binary variable is the pullback
along the value map

```text
v_(c,x):R_c->{-1,+1}.                                      (FGD1)
```

The strict common refinement of this finite-set diagram is

```text
Omega={ (a_c)_c in product_c R_c :
        a_c(x)=a_d(x) for every shared variable x }.       (FGD2)
```

Every strict realization of all context diagonals as coarse object
diagonals on a nonempty finite sheet set factors through `(FGD2)`: a sheet
records one atom `a_c` in each context, and literal equality of the two
coarse shared-variable projections says exactly that the recorded values
agree.  Conversely every `omega in Omega` gives such a sheet.  Hence

```text
Omega is nonempty  iff  the BCS has a classical solution.  (FGD3)
```

For the fixed BCS with a tracial model but no `R^U` model, `Omega` is empty.
Thus its finite diagram of coarse diagonal inclusions has no nonzero unital
strict object-diagonal realization.  Pairwise groupoid coverings or spans
do not alter this conclusion: after choosing paths to one root fiber, either
their sheet transports remain as arrows, in which case shared marginals are
only conjugate, or the marginals are literally identified and each root
sheet is a point of `Omega`.

Passing to a connected object corner does not hide this obstruction.  If
`Gcal` is a connected discrete groupoid with `n` objects and isotropy group
`H` at `o`, then

```text
C[Gcal] isomorphic to M_n(C[H]),
q C[Gcal] q isomorphic to C[H],       q=1_o.              (FGD4)
```

For the native object diagonal `Delta=sum_y C 1_y`,

```text
q Delta q=Cq.                                             (FGD5)
```

Moreover, transporting any other object identity back to `o` by an arrow
turns it into `q`; compression does not turn the object set into distinct
projections in `C[H]`.  If one retains `r` objects instead, the finite
amplification is `M_r(C[H])` and its compressed native diagonal is the one
common diagonal `C^r`.  All context coarse partitions inside it again have
the common sheet refinement `(FGD2)`.

There are therefore only three outcomes for the proposed finite-groupoid
compiler.

1. Keep the arrows and their cycle holonomy: one gets covariance, not the
   overlap equality `(BPA3)`.
2. Impose literal equality: the object labels form `Omega`, so a nonzero
   model is classical.
3. Replace object projections by non-diagonal elements of `C[H]`: this has
   left the object/covering construction.  For a graph of finite groupoids,
   `H` is virtually free, and even arbitrary such corner elements are
   excluded by the CE canonical-corner argument (also after a fixed matrix
   amplification).  For an isotropy group created by additional two-cell
   relations, preserving the finite packet while imposing those relations
   is precisely the signed-Hecke relative holonomy problem.

Thus finite groupoids do not supply a new common-corner promotion.  Their
Morita equivalence is not a unital embedding of the whole matrix groupoid
algebra into one object corner: it either erases the object projections or,
after finite amplification, retains one common classical diagonal.  The
first genuinely open operation remains a non-diagonal, block-escaping chord
in an infinite group-algebra corner.
