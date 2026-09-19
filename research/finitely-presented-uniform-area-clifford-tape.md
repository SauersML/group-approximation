---
rg: 2
id: finitely-presented-uniform-area-clifford-tape
kind: claim
title: Build a finitely presented common-sign Clifford tape with uniformly bounded table area
distinct_from:
  thompson-clifford-central-product-tape: that supplies a finitely presented exact tape with a common nontrivial sign; this asks for the missing uniform area bound for every finite packet multiplication table.
  adaptive-all-pairs-schur-replica-table-compiler: that activates one rank chosen by a halting computation; this asks one fixed group to contain all ranks simultaneously and uses no self-reference.
artifacts:
  - research/artifacts/static-challenger-occurrence-hs-breaker-2026-08-20.md
---

OPEN.  Construct a finite presentation `Gamma=<S|R>`, a nontrivial word `j`,
and representatives `sigma_N:E_N->F(S)` for every finite extraspecial Pauli
group such that `sigma_N(J)=j` and the multiplication discrepancies satisfy
the uniform area bound `(BAC2)`.

The exact Thompson--Clifford tape supplies all algebraic packets, but its
remote cells have multiple names differing by stabilizer words.  Present
estimates pay the length/area of those stabilizer comparisons, and coherent
small rotations show that this loss cannot simply be discarded.  A solution
must either choose canonical addresses whose table identities are literal
conjugates of bounded prototypes, or add a bounded-area coherence mechanism.

By `uniform-bounded-area-clifford-tables-force-mark-collapse`, this one claim
would itself exhibit a finitely presented nonhyperlinear group.

## Attempts

- **Thompson--Clifford tape.**  It contains every exact packet with the common
  sign, but alternative cell names differ by stabilizer words of growing
  length; the resulting multiplication-table areas are not uniform.
- **Literal conjugacy representatives.**  Transporting one prototype relation
  by conjugacy is free in HS norm, but multiplication of two independently
  addressed cells introduces the unresolved comparison of their transporter
  names.
- **High-order Weyl compression.**  It reduces the number of generators but
  its phase/determinant obstruction has vanishing normalized-HS strength and
  does not imply `(BAC3)`.
