---
rg: 2
id: stw99-eckhardt-wu-decomposition-rank-conjecture
kind: claim
title: An elementary amenable group has finite decomposition rank iff it has polynomial growth (STW Problem LXXXVI)
root: true
distinct_from:
  stw99-problem-lxxxiv-nuclear-dimension-amenable-groups: that asks to compute nuclear dimension across all amenable groups; this is the Eckhardt--Wu conjecture pinning the finer invariant, decomposition rank, to polynomial growth on the elementary amenable class.
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
---

**Problem LXXXVI of Schafhauser--Tikuisis--White, arXiv:2506.10902** (Eckhardt--Wu, [121, Conjecture II]).  For a
finitely generated elementary amenable group `G`: `C*(G)` has finite
decomposition rank if and only if `G` has polynomial growth.

The forward implication is the open one; polynomial growth gives finite
decomposition rank (Eckhardt--Gillaspy--McKenney).  The lamplighter shows
decomposition rank and nuclear dimension genuinely diverge here: strong
quasidiagonality is the obstruction (Carrión--Dadarlat--Eckhardt), which is
the same quasidiagonality axis as the repository's MF-radical program, one
level up (all traces, uniformly).

## Attempts

* Neither Chou's growth results nor the solved `Z^d ⋊ Z` case reduce the
  full forward implication to Berend actions.  They instead motivate the
  concrete subproblem `stw99-lxxxvi-berend-groups-decomposition-rank`: the
  Berend-type `Z^3 ⋊ Z^2` are strongly quasidiagonal
  (`berend-torus-actions-give-strongly-qd-polycyclic-groups`), so the
  Kirchberg--Winter obstruction that settles the `Z^d ⋊ Z` case is provably
  silent.  An entropy-versus-decomposition-rank implication for these
  algebraic actions is one possible new mechanism, not a known reduction
  of the general conjecture.
