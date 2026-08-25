---
rg: 2
id: balanced-schur-reynolds-first-hit-placement
kind: claim
title: Place balanced Schur-Reynolds companions in successive first-hit bands
distinct_from:
  proper-corner-charged-section: That constructs one payload-oriented source and paid complement; this must identify successive copies with the active Toeplitz/Fanizza child and make the complements summable.
  index-two-reynolds-atoms-have-orthogonal-hnn-transports: That routes a fixed finite family to orthogonal character atoms; this needs a coherent level-by-level placement with one persistent active branch.
  toeplitz-schur-child-masa-recurrence: That asks for the full child-packet recurrence; this uses only the balanced companion source and the phase-selected branch required by the first-hit scalar ledger.
---

**OPEN GLOBAL PLACEMENT.**  Fix the robust non-CE BCS and a depth `N`.
Attach one balanced two-sign Reynolds/Schur cell to each forbidden assignment
at levels `0,...,N-1`.  Couple its source projection to the active corrected
Schur child at that level and transport its unused complement to a fresh
first-hit band so that every canonical finite matrix microstate produces
numbers `q_n,r_n` satisfying

```text
2q_n <= q_(n+1)+r_n+C p(n)sqrt(E),
r_n <= q_n+C p(n)sqrt(E),
r_n >= eta q_n-C p(n)sqrt(E),
sum_(n<N) r_n <= 1+C P(N)sqrt(E),                       (BSR1)
```

with fixed `eta>0`, a fixed polynomial `p`, and constants independent of
matrix dimension.  Marked separation and the robust BCS gap must give
`q_0>=q_*>0`.

The local ingredients are already exact.  The two-sign transvection gives a
source and exit of equal trace on each selected atom; the Schur flip-square
word orients the raw phase on that source; the binary Schur restriction
gives the factor two; and marked index-two transports can move exits to
orthogonal finite character atoms.  The open assertion is their **common
incidence across levels**: the surviving child at level `n` must be the
source used at level `n+1`, while the discarded companions must be genuine
first-hit projections rather than a stationary reuse of one multiplicity
space.

The finite presentation must retain an exact infinite tracial model.  In the
perfect BCS model every forbidden atom is zero, so all balanced Reynolds
sources and exits vanish and the added cells are vacuous; the marked payload
sign remains nontrivial.  Thus `(BSR1)` is required only for canonical finite
matrix microstates, through the robust BCS selection, not as a universal
finite-trace identity.

## Attempts

- **Route every level to a distinct character of one finite elementary
  abelian packet.**  This gives literal orthogonality, but it is
  trace-functorial.  The regular representation of the resulting finite
  Bass--Serre actor carries the stationary type vector, so the total source
  Plancherel mass cannot exceed the available character capacity.  Enlarging
  the packet only dilutes each destination by the same factor.
- **Put the local exits in the disjoint polynomial degree bands directly.**
  The coefficient bands are disjoint, but their spectral support projections
  need not be: one finite-dimensional coefficient character may be nontrivial
  on many bands.  The missing incidence must use a first-detection projection
  or an equivalent matrix-only selection, not monomial-degree disjointness
  alone.
- **Repeat the balanced local cell around a finite cycle.**  The phase is now
  oriented, but the companion multiplicities still admit a stationary flow
  around the cycle.  The live attack is to couple the phase-selected branch
  to the Toeplitz/Fanizza first-hit flag so reuse of an earlier companion is
  charged by the boundary reservoir.

## Attempts

Choosing the finite character atoms independently at each depth proves local
orthogonality but does not identify the surviving child at level `n` with the
source at level `n+1`; the recurrence then has unrelated `q_n`.  Reusing one
stationary multiplicity atom repairs that identification but makes the exits
overlap, so the bound on `sum r_n` fails.  A successful construction must
encode both identifications in the same incidence system.

- **The complete fixed-depth packet/HNN assembly has an exact marked matrix
  countermodel.**  `balanced-schur-finite-depth-reuse-is-regular-absorbed`
  observes that the balanced Schur square is contained in a finite
  semidirect vertex packet and that dressing the Reynolds section adds no
  second edge relation.  Full-child reuse and finite first-hit transports
  are still only finite-subgroup HNN covariance.  Common negative regular
  multiples therefore extend across every row and give an exact model with
  payload sign `-I`.  Hence independent covariance rows cannot imply
  `(BSR1)`; a load-bearing cross-edge multiplicity/support relation is
  necessary.
