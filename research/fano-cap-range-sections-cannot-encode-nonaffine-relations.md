---
rg: 2
id: fano-cap-range-sections-cannot-encode-nonaffine-relations
kind: claim
title: A Fano-cap-range witness section cannot pp-encode a nonaffine relation
distinct_from:
  affine-auxiliary-control-flow-barrier: that says a gadget built from affine constraints has affine visible projection; this begins with nonlinear R-star constraints and proves that one cap-range completeness section would allow every used constraint to be replaced by an affine one.
  rstar-fano-ghost-affine-hull-criterion: that treats one local support; this applies all local affine hulls simultaneously to a complete pp-gadget and constrains its visible source relation.
  culf-mastel-rstar-reduction-is-support-blind: that observes the published reduction gives no cap-range promise; this proves such a promise is impossible whenever the encoded source relation is nonaffine and the completeness section covers all of it.
---

ESTABLISHED.
Let a finite pp-gadget over `R_*` have visible variables `x`, auxiliary
variables `y`, solution set

```text
T subseteq F_2^(x,y),       projection_x(T)=C.                    (FCR1)
```

Suppose there is a section `sigma:C -> T` of the visible projection.  For
each occurrence `j` of the `R_*` predicate, let

```text
S_j={the local j-tuple of sigma(c):c in C} subseteq R_*.          (FCR2)
```

If every translated `S_j` is a Fano cap, then `C` is affine.

Indeed, put `A_j=Aff(S_j)`.  The Fano criterion gives `A_j subseteq R_*`.
Let `T_aff` be the solution set obtained by replacing every gadget occurrence
by the affine equations cutting out `A_j`.  Then `T_aff` is affine and

```text
sigma(C) subseteq T_aff subseteq T.                              (FCR3)
```

After visible projection, `(FCR1)` and `(FCR3)` give

```text
C subseteq projection_x(T_aff) subseteq C,                       (FCR4)
```

so equality holds.  A projection of an affine set is affine, proving the
claim.

Consequently a classical NP reduction of a genuinely nonaffine source
constraint to `R_*` cannot lift **all** source satisfying assignments through
one deterministic witness choice while keeping cap range in every target
constraint.  Any cap-supported Culf--Mastel completeness lift must exploit a
proper support of the source perfect trace or global contextual correlations;
it cannot follow from a cap-range refinement of the classical pp reduction
on the full source relation.
