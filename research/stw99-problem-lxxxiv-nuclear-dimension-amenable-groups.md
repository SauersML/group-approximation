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

There is now a nonabelian quotient obstruction which can remain effective
when that rank is zero.  `stw84-wreath-quotient-obstruction` proves that every
countable amenable group surjecting onto `K wr H` has infinite-dimensional
group C*-algebra whenever `K` is infinite virtually polycyclic and `H` is
infinite finitely generated virtually nilpotent.  In particular
`D_infinity wr D_infinity` has finite abelianization but infinite nuclear
dimension, and the same conclusion holds for all its countable amenable
extensions.

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

The direct-product hypothesis can now be replaced by a controlled extension
hypothesis.  `stw84-kernel-finite-locally-finite-by-abelian-computation`
proves that an exact sequence

```text
1 -> L -> G -> A -> 1
```

with `L` locally finite and `A` abelian satisfies

```text
dim_nuc(C*(G))=rank_Q(A)
```

whenever every finitely generated `H subset G` has finite `H intersection L`.
This includes nonsplit extensions.  For split extensions it is enough that
every finite subset of `L` has finite orbit-generated hull under every
finitely generated subgroup of `A`.  Cyclically rotating finite blocks of
unbounded size gives a nontrivial `L rtimes Z` example which is not virtually
abelian but has nuclear dimension exactly one.

## Attempts

The locally finite factor argument depends on the augmentation quotient
`C*(L times H)->C*(H)` and does not survive an arbitrary semidirect product.
The kernel-finite extension theorem handles locally finite orbit-hulls, but
does not cover shift actions such as the lamplighter action, where a finitely
generated subgroup can meet the locally finite kernel in an infinite group.
The directed-union argument also needs a uniform bound; it gives no control
when the Hirsch lengths of finitely generated subgroups diverge.  Thus the
remaining frontier includes unrestricted locally-finite-by-abelian groups
and the general finite-Hirsch-length elementary amenable conjecture.  The
wreath-quotient theorem gives a robust negative class but does not provide a
converse: absence of such a quotient is not known to imply finite nuclear
dimension.
