---
rg: 2
id: finite-failure-ledgers-do-not-bypass-source-gram
kind: claim
title: Finite induced failure ledgers name every Gram deficit but do not bypass common-source saturation
distinct_from:
  common-source-hnn-bridges-need-one-gram-saturation-identity: that isolates the total selected source-Gram deficit; this decomposes that deficit into every nonselected induced type and audits whether routing those pieces closes the argument.
  isotypic-finite-edge-forces-full-commuting-selector-support: that obstructs a single saturated finite edge type; this permits all unwanted induced types and tests the alternative of charging them separately.
  positive-overlap-curvature-collapses-carrier: that closes the analytic mark-collapse ledger once a mark-relative capacity surplus and localized non-CE energy are supplied; this proves that finite failure tags alone supply neither missing hypothesis.
---

## Verdict

Decomposing every source-Gram deficit into the nonselected irreducible types
of the finite induced packet is exact, effective, and useful bookkeeping.  It
does **not** remove `(CSG4)`.

There are two separate losses.

1. On the full finite-edge isotypic source, the failure pieces are honest
   orthogonal projections.  On the actual analytic source
   `Q=(1-C)E`, their compressions are only a POVM unless `Q` reduces the
   packet-type projections.  Finite induction theory does not control this
   new commutator.
2. Even in the best projection-valued case, disjoint failure tags prove only

   ```text
   total failure mass <= available capacity + tag/route energy. (FFL1)
   ```

   A fixed finite capacity may absorb all the failures at zero energy.  The
   accepted intersection can then be zero, or can fail to reduce the shared
   logical tuple.  Canonical Plancherel weights do not break this symmetry;
   they give an exact stationary failure ledger.

Thus a failure decomposition becomes decisive only after adding either the
original source-Gram saturation, or the same mark-relative capacity surplus
and mixed non-CE localization required by the positive-overlap route.  It is
not a third way around the common-carrier problem.

## Attempts

- **Route every nonselected induced type into one disjointly tagged
  capacity.**  This gives the valid estimate `(FFL13)` but dies because the
  fixed capacity can absorb positive canonical Plancherel mass; the Klein
  four model in Section 4 has zero energy and zero accepted intersection.
- **Decode on the intersection of the selected complements.**  This dies
  before BCS soundness: owner-context covariance does not make that
  intersection reduce variables from the other contexts, as `(FFL21)--(FFL22)`
  show.
- **Choose a smaller capacity and use proper infiniteness for completeness.**
  The exact HALT model permits this, but finite packet data cannot make the
  over-capacity routing a universal consequence without contradicting the
  regular trace.  A matrix-only mixed non-CE localization theorem is still
  required.

## 1. Exact finite induction decomposition

Let `H<=G` be finite, let `sigma` be an irreducible representation of `H`,
and write

```text
Ind_H^G(sigma)=directSum_(rho in dual(G)) m_rho rho,
m_rho=dim Hom_H(sigma,Res_H^G rho).                    (FFL2)
```

Let `e_sigma in C[H]` and `p_rho in Z(C[G])` be the corresponding central
idempotents.  In an exact HNN packet representation with bridge unitary `U`,
put

```text
P_rho=e_sigma U^*p_rho U e_sigma.                     (FFL3)
```

Because `U^*p_rho U` commutes with the source copy of `H`, it preserves every
`H`-isotypic subspace and commutes with `e_sigma`.  Consequently the nonzero
`P_rho` are mutually orthogonal projections and

```text
sum_(rho:m_rho>0) P_rho=e_sigma.                       (FFL4)
```

For a chosen set `A` of allowed/selected target types, the selected Gram and
failure projection are therefore

```text
A_sel=sum_(rho in A)P_rho,
F_fail=e_sigma-A_sel=sum_(rho notin A)P_rho.           (FFL5)
```

Everything in `(FFL2)--(FFL5)` is computable from the two finite character
tables and the restriction matrix.  Hence there is no classification
obstruction to naming each failure channel separately.

### Canonical Plancherel weights

In the normalized regular trace of `G`, each channel has the exact weight

```text
tau_G(e_sigma p_rho)
 = d_sigma d_rho m_rho/|G|,                            (FFL6)
```

where `d_sigma=dim sigma` and `d_rho=dim rho`.  Indeed the `rho`-block occurs
with regular multiplicity `d_rho`, and its `sigma`-isotypic subspace has
dimension `m_rho d_sigma`.  Summing `(FFL6)` gives

```text
sum_rho tau_G(e_sigma p_rho)
 =d_sigma^2/|H|=tau_G(e_sigma),                        (FFL7)
```

by `dim Ind_H^G(sigma)=[G:H]d_sigma`.

Canonical-profile matrix microstates reproduce these numbers.  In
particular, the unwanted induced summands have fixed **positive** mass; trace
conditioning does not make them disappear.

## 2. Compression to the analytic source destroys the type PVM

The common-source cell does not use all of `e_sigma`.  It uses an analytic
off-capacity carrier

```text
Q=(1-C)E <= e_sigma.                                   (FFL8)
```

For one target type define

```text
V_rho=p_rho UQ,
F_rho=V_rho^*V_rho=Q U^*p_rho UQ.                     (FFL9)
```

The `F_rho` are positive contractions and

```text
sum_rho F_rho=Q,                                      (FFL10)
```

but they need not be projections or mutually orthogonal.  They form a POVM.
They are a projection-valued decomposition exactly when

```text
[Q,U^*p_rho U]=0                                      (FFL11)
```

for every relevant `rho`.  Thus the proposed failure ledger has already
reintroduced a source-reduction condition before any tag is attached.
Spectral-cutting or polar-rounding the effects in `(FFL9)` loses an amount
controlled by the same missing commutators.

This is not fixed by observing that `Q<=e_sigma`: the commutant of the source
`H`-action on its `sigma`-isotypic component is the full multiplicity matrix
algebra.  The projections `Q` and `P_rho` may be arbitrary noncommuting
projections in that algebra.

## 3. What a perfect finite tag ledger actually proves

Grant the strongest favorable situation: the failure effects have been
upgraded to projections `F_a`, and partial isometries route them into one
capacity projection `C`.  Give their target ranges pairwise disjoint exact
types of a fixed finite tag group.  The finite-group intertwiner Laplacian
then makes all pairwise range overlaps pay tag-covariance energy.

At zero error the tagged ranges are orthogonal subprojections of `C`, so

```text
sum_a tau(F_a)=sum_a tau(R_a)<=tau(C).                 (FFL12)
```

With approximate covariance, the same Gram-capacity calculation and the
finite tag gap give

```text
sum_a tau(F_a)
 <=tau(C)+K_tag E_tag+K_route E_route.                 (FFL13)
```

The constants depend only on the fixed finite ledger, not on matrix
dimension.  This is a valid positive conclusion, but it is only `(FFL1)`.
It does not imply

```text
sum_a tau(F_a)->0                                     (FFL14)
```

unless one also proves that the available capacity tends to zero.  The
useful alternative is a mark-relative surplus

```text
sum_a tau(F_a)-tau(C)>=a tau(P)-o(1),                 (FFL15)
```

which is exactly the capacity hypothesis used by
`positive-overlap-curvature-collapses-carrier`.  Neither `(FFL14)` nor
`(FFL15)` follows from the finite induction decomposition.

Parent-exclusive placement of every failure type inside `C` does not come
for free either.  It is the hypothesis `(DTC5)` of
`disjoint-tag-covariance-controls-cross-gram`.  The finite induction barrier
says that compatible tag/selector characters occur in induced
representations outside the intended parent as well.  Any uncharged outside
component becomes a new source-Gram deficit, merely moving the ledger one
edge farther out.

## 4. Exact canonical countermodel to the proposed dichotomy

The obstruction already appears in the regular representation of the Klein
four group

```text
K=C_2 x C_2.                                           (FFL16)
```

Take `H={1}`, `sigma=1`, so `Ind_H^K(sigma)` is the regular representation.
Let `e_1,...,e_4` be its four primitive Fourier projections.  They satisfy

```text
tau(e_c)=1/4,
e_c e_d=0 (c!=d),
sum_c e_c=1.                                          (FFL17)
```

For four contexts choose the selected projection and its failure by

```text
p_c=1-e_c,
F_c=e_c.                                              (FFL18)
```

Every failure has its own disjoint finite character tag.  Take the common
capacity `C=1` and route each `F_c` by its identity inclusion.  Then all
packet, tag, and routing equations are exact; the canonical Plancherel
weights are exact; and the capacity ledger is saturated:

```text
sum_c tau(F_c)=tau(C)=1.                              (FFL19)
```

Nevertheless

```text
meet_c p_c=0.                                         (FFL20)
```

Thus there is neither a common accepted carrier nor positive tag/capacity
energy.  This is a literal finite induction decomposition, not a diffuse or
noncanonical representation.

Choosing a smaller formal capacity would force an overlap floor in finite
trace, but ordinary finite packet relations cannot impose an exact
over-capacity family: the left regular representation of the resulting group
is itself a finite tracial representation of all universal word relations.
To make the smaller-capacity conclusion matrix-only rather than universally
tracial, one must consume the shared non-CE tuple.  That is precisely the
missing localized two-cell, not a consequence of the failure tags.

## 5. Accepted intersection still need not decode the BCS

Even a positive accepted intersection is not enough unless it approximately
reduces **every** shared logical observable.  Context covariance controls
`[A_c,Z_x]` only when `x` belongs to context `c`.  The intersection depends
on all the other `A_d`, whose commutators with `Z_x` are uncontrolled.

The two-dimensional example is exact.  Put

```text
Z=diag(1,-1),
A_1=I,
A_2=|+><+|,
|+>=(1,1)/sqrt(2).                                    (FFL21)
```

The owning-context condition gives `[A_1,Z]=0`.  The accepted intersection
is `R=A_1 meet A_2=A_2`, but

```text
||[R,Z]||_2^2=1.                                      (FFL22)
```

A subprojection of a reducing projection need not reduce the same operator;
here even the first selected projection is the identity.  No estimate for
`[R,Z]` can depend only on the owner-context commutator.

To control `(FFL22)` one must bound `[A_d,Z_x]` for the cross-context pairs as
well.  Those are exactly the mixed shared-tuple terms isolated by
`capacity-gated-common-corner-bcs-two-cell` and `(NCL13)`.  Assuming merely
that `Q` reduces all `Z_x` would not by itself make an arbitrary meet of
nonreducing `A_c` reduce them; one needs the full mixed covariance row.

## 6. Exact HALT extension is not the obstruction

The finite failure atlas extends cleanly on the HALT side.  Gauge-covariantize
the exact BCS witness, amplify countably, and give every one of the finitely
many selected and failure types infinite multiplicity.  A properly infinite
capacity carrier contains mutually orthogonal copies of all failure
carriers, so the routing and tag relations can be implemented exactly.  If
the forbidden source vanishes, the whole failure ledger may simply be zero.

This confirms that completeness is permissive.  It does not yield finite
soundness.  The group also has its left regular tracial representation, so a
finite rank/capacity contradiction cannot be a universal consequence of the
word relations.  Its finite-dimensional-only step must still come from the
non-CE localized moment gap or another matrix-coordinate theorem.

## 7. Corrected use of the failure decomposition

The decomposition `(FFL5)` remains worthwhile because it gives a finite,
explicit list of leakage channels.  A valid compiler may attach disjoint tags
to those channels and then prove both

```text
mark-relative failure surplus:  sum_a tau(F_a)-tau(C)>=a tau(P)-o(1),
mixed localization:             Lambda<=K E_rel+o(1).  (FFL23)
```

The positive-overlap curvature theorem would then collapse `P` without full
source-Gram saturation.  But `(FFL23)`, especially the cross-context mixed
localization and parent-exclusive placement, is the load-bearing matrix-only
content.

Alternatively, proving all failure masses vanish recovers `(CSG4)` and the
original common-source decoder.  Therefore the finite failure ledger offers
a useful coordinate system for the remaining mixed actuator, but it does not
close the Fanizza groupifier on its own and does not avoid the requirement
that the accepted or leakage carrier be controlled against the whole shared
tuple.
