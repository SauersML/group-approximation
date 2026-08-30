---
rg: 2
id: stw63-semifinite-rank-uniqueness-proof
kind: route
title: Split the center and force all properly infinite support ranks to equal the unit
target: stw63-semifinite-von-neumann-codomains-have-uniqueness
requires: []
artifacts:
  - research/artifacts/stw63-z-embedding-audit-2026-08-30.md
---

First suppose that `M` is finite; no countability hypothesis is needed in
this case.  Let `Phi:M->Z(M)` be its center-valued trace.  Every state
`omega` on `Z(M)` makes `omega Phi phi` and `omega Phi psi` tracial states
on `Z`, so uniqueness of the trace of `Z` gives

```text
Phi phi(a)=tau_Z(a)1=Phi psi(a)                 (a in Z).    (0)
```

The finite-von-Neumann uniqueness theorem for strongly LF-embeddable
domains applies because `Z` is ASH, and gives approximate unitary
equivalence.  Its formulation permits a net of unitaries; since `Z` is
separable, the usual finite-set diagonal extraction gives a sequence.

It remains to treat a semifinite `M` acting on a separable Hilbert space.
Let `z_f` be the largest central projection for which `z_f M` is finite.
Write

```text
M = M_f directSum M_infinity,
M_f=z_f M,                 M_infinity=(1-z_f)M.              (1)
```

Both central compressions of a unital embedding of the simple algebra `Z`
are unital embeddings whenever the summand is nonzero.

On `M_f`, let `Phi:M_f->Z(M_f)` be the center-valued trace.  For every state
`omega` on the center, the scalar maps

```text
omega Phi phi,             omega Phi psi
```

are tracial states on `Z`, and hence both equal its unique trace `tau_Z`.
States separate the center, so

```text
Phi phi(a)=tau_Z(a)1=Phi psi(a)                 (a in Z).    (2)
```

The Jiang--Su algebra is ASH and therefore strongly LF-embeddable.  The
finite-von-Neumann uniqueness theorem for strongly LF-embeddable domains
turns (2) into approximate unitary equivalence in `M_f`.

Now work in `M_infinity`, which has no nonzero finite central summand.  Fix
`0!=a in Z` and let `p` be the range projection of `phi(a)`.  The positive
element `a*a` is full in the simple unital algebra `Z`.  Compactness of the
unit, or the elementary finite-sum fullness criterion, gives a finite `n`
such that

```text
1_Z <=_Cu (a*a) directSum ... directSum (a*a)   (n copies).
```

After applying `phi` and passing to support projections,

```text
1_(M_infinity) <=_MvN p directSum ... directSum p.           (3)
```

Relation (3) makes the central support of `p` equal to one.  Moreover `p`
has no nonzero finite central part: if `0!=z` were central and `zp` finite,
then `n(zp)` would be finite, while (3) would make the unit `z` of `zM`
subequivalent to it.  This would make `zM` a finite central summand, contrary
to (1).  Thus `p` is a full properly infinite projection.  In the
countably-decomposable semifinite algebra `M_infinity`, full properly
infinite projections are Murray--von Neumann equivalent to the unit, so

```text
M_infinity-rank(phi(a))=[1].                                (4)
```

The same argument gives (4) for `psi(a)`; the zero element has rank zero.
Therefore `phi` and `psi` have the same von Neumann rank on every element of
`Z`.  The ASH rank-uniqueness theorem for a semifinite von Neumann algebra
with no finite summand now gives norm approximate unitary equivalence in
`M_infinity` (indeed, in its compact-relative form).

Taking the direct sum of the implementing unitaries in the two summands of
(1), with one common finite-set tolerance, proves approximate unitary
equivalence in `M`.

The imported results are exactly the finite center-valued-trace theorem and
the no-finite-summand ASH rank theorem of Li--Hadwin--Liu, documented in the
artifact.  The support-rank collapse (3)--(4) and the central splitting
application to `Z` are internal.
