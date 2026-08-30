---
rg: 2
id: stw99-problem-lxvi-car-embedding-with-finite-projection
kind: claim
title: A simple infinite C*-algebra contains a unital CAR algebra whose image has a nonzero finite projection (STW Problem LXVI)
root: true
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
---

**Problem LXVI of Schafhauser--Tikuisis--White, *Nuclear C\*-algebras:
99 problems*, arXiv:2506.10902v2.**  Does there exist a simple unital infinite
C\*-algebra `B` and a unital embedding

```text
phi : M_(2^infinity) -> B
```

whose image contains a nonzero finite projection?

The problem is open.  Rordam's mixed finite/infinite simple algebra gives the
finite-stage analogue with `M_2` in place of the CAR algebra.  The exact
corner reduction `stw99-lxvi-iff-finite-car-corner-with-infinite-double`
shows that the remaining issue is not coherence of infinitely many matrix
units by itself: it is whether a unital CAR algebra can live inside a simple
finite algebra whose `2 x 2` amplification is infinite.

## Attempts

The active attack is `stw99-lxvi-via-finite-car-corner`.  It reduces the
problem to one construction rather than deferring it: build the CAR algebra
inside a finite simple corner while its double is already infinite.
