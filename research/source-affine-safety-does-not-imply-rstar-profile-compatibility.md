---
rg: 2
id: source-affine-safety-does-not-imply-rstar-profile-compatibility
kind: claim
title: Source affine safety does not imply compatibility with one R-star cap profile
distinct_from:
  fano-cap-witness-sections-force-source-affine-safety: that proves affine safety is necessary for a cap-valued lift; this explicit three-row gadget proves it is not sufficient.
  rstar-core-character-profiles-induce-an-exact-affine-cover: that gives the exact affine-piece containment criterion; this exhibits an affine-safe support crossing all of its pieces.
---

**ESTABLISHED FINITE COUNTEREXAMPLE.**  Let the visible variables be
`p,q,r`, let `a,b,c,d` be auxiliary variables, and impose the three ordered
rows

```text
R_*(q,p,a,b),    R_*(a,c,r,q),    R_*(r,q,d,b).          (ASC1)
```

Their visible projection is all of `F_2^3`.  In particular the affine plane

```text
S={(p,q,r):p+q=1}                                      (ASC2)
```

is affine-safe in the source relation.

Nevertheless no deterministic witness section on `S` has cap range in all
three rows.  The `R_*` conditions force a unique witness above every member
of `S`, and the first row ranges over

```text
{1011,0100,0111}.                                      (ASC3)
```

After ghost translation the corresponding tail points are
`011,100,111`, which form a Fano line.  Hence the first row is not contained
in any maximal cap, so no single seven-character profile contains `S`.

All three rows survive pinned two-tail peeling with `p,q,r` pinned: `c` and
`d` are the only degree-one auxiliaries, one in each of the last two rows,
while `a,b` are shared.  Thus `(ASC1)` is a small explicit certificate that
the dense-core compatibility problem is strictly stronger than source
affine safety.
