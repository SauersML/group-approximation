---
rg: 2
id: stw99-problem-lxxxvii-roe-algebra-nuclear-dimension
kind: claim
title: Nuclear dimension of the uniform Roe algebra equals asymptotic dimension (STW Problem LXXXVII)
root: true
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
  - research/artifacts/stw87-lxxxvii-uniform-roe-nuclear-dimension-audit-2026-08-30.md
---

**Problem LXXXVII of Schafhauser--Tikuisis--White, arXiv:2506.10902** (Willett--Winter, [449, Question 9.5]).  For a
countable discrete bounded-geometry metric space `X`, is
`dim_nuc(C*_u(X))` equal to the asymptotic dimension of `X`?

Asymptotic dimension is an upper bound (Willett--Winter).  Finite-valued
positive answers are known only in asymptotic dimension zero (equivalently
`C*_u(X)` AF) and one; even `X = ℤ²` is open, and STW record that at least one
author expects a negative answer.  Li--Liao--Winter's diagonal dimension of
`ℓ^∞(X) ⊆ C*_u(X)` does equal the asymptotic dimension, so the question is
whether nuclear dimension sees the diagonal.

The equality is also automatic, with both sides infinite, when `X` does not
have property A.  Thus the unresolved cases split into finite asymptotic
dimension at least two and property-A spaces of infinite asymptotic dimension.
A search of primary-source title/abstract records through 2026-08-30 found no
later theorem settling either part.

## Attempts

Winter--Zacharias prove the upper bound.  Li--Willett prove the reverse
implication at asymptotic dimension zero, which together with the upper bound
also settles value one.  Sako's equivalence between property A and nuclearity,
combined with the Winter--Zacharias bound and the fact that finite nuclear
dimension implies nuclearity, settles every space without property A at the
value infinity.

For a subset `Y ⊆ X`, compression by `χ_Y` identifies the corner
`χ_Y C*_u(X) χ_Y` with `C*_u(Y)`.  Nuclear dimension therefore gives a
monotone lower-bound mechanism from subspaces, but no seed with nuclear
dimension at least two is presently known.  This mechanism now extends from
subspaces to arbitrary coarse embeddings: after uniformly labelling the
finite fibres, `C*_u(Y)` is a diagonal hereditary corner of a finite matrix
amplification of `C*_u(X)`
(`stw87-coarse-embedding-corner-lower-bound`).  Thus equality propagates from
any coarsely embedded full-asymptotic-dimension seed, and unbounded
nuclear-dimension seeds force infinite nuclear dimension.  Finally, the
canonical diagonal expectation has exact distance `1/2` from every diagonal
c.p.c. order-zero repair on a fixed two-point *-homomorphism.  Thus
diagonal-dimension equality cannot be converted to the missing lower bound by
averaging arbitrary nuclear approximations, even followed by an arbitrarily
small order-zero perturbation.
