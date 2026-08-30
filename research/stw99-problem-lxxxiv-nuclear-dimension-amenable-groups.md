---
rg: 2
id: stw99-problem-lxxxiv-nuclear-dimension-amenable-groups
kind: claim
title: Determine which amenable groups have group C*-algebras of finite nuclear dimension (STW Problem LXXXIV)
root: true
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
  - research/artifacts/stw84-local-rank-and-locally-finite-factor-audit-2026-08-30.md
---

**Problem LXXXIV of Schafhauser--Tikuisis--White, arXiv:2506.10902.**  Determine for which countable discrete amenable
groups the group C\*-algebra has finite nuclear dimension; better, compute it.

Known: polynomial growth gives finite decomposition rank (Eckhardt--Gillaspy--
McKenney); finitely generated virtually polycyclic groups have finite nuclear
dimension bounded by the Hirsch length (Eckhardt--Wu, STW Theorem 40);
`C*(ℤ≀ℤ)` has infinite nuclear dimension (from Giol--Kerr), while the
lamplighter `(ℤ/2)≀ℤ` has finite nuclear dimension but not finite
decomposition rank (it is not strongly quasidiagonal).  Eckhardt--Wu
conjecture: finite nuclear dimension iff finite Hirsch length.

## New reductions and exact classes

The lower-bound theorem `stw84-abelianization-rank-lower-bound` shows that
finite nuclear dimension forces the abelianization to have finite rational
rank.  This gives an immediate infinite-dimensional certificate for every
amenable group surjecting onto an infinite-rank abelian group.

The inductive-limit theorem `stw84-directed-union-uniform-bound` passes a
uniform nuclear-dimension bound from an increasing exhaustion by amenable
subgroups to the whole group.  Combined with the exact finitely generated
virtually abelian calculation, it proves
`stw84-locally-virtually-abelian-uniform-rank`: a countable locally virtually
abelian group of finite uniform local Hirsch rank `r` has nuclear dimension at
most `r`, with equality whenever its abelianization has rational rank `r`.

Combined instead with Eckhardt--Wu's uniform virtually-polycyclic bound, the
same limit theorem proves `stw84-locally-virtually-polycyclic-uniform-hirsch`:
uniformly bounded Hirsch length across all finitely generated subgroups is
enough for finite nuclear dimension, even when the countable union is not
itself virtually polycyclic or virtually solvable.

There is also an exact permanence theorem independent of virtual abelianness.
`stw84-locally-finite-direct-factor-invariance` proves that adjoining any
countable locally finite direct factor changes no nuclear dimension.  Hence
`stw84-locally-finite-times-abelian-computation` computes

```text
dim_nuc(C*(L times A))=rank_Q(A)
```

for every countable locally finite `L` and countable abelian `A`, including
infinite rank and non-virtually-abelian products.

## Attempts

The locally finite factor argument depends on the augmentation quotient
`C*(L times H)->C*(H)` and does not survive an arbitrary semidirect product.
The directed-union argument also needs a uniform bound; it gives no control
when the Hirsch lengths of finitely generated subgroups diverge.  Thus the
remaining frontier includes nonsplit locally-finite-by-abelian groups and the
general finite-Hirsch-length elementary amenable conjecture.
