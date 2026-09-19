---
rg: 2
id: leavitt-three-gate-kernel-picture-has-area-at-least-six-proof
kind: route
title: Enumerate planar trivalent ribbon pairings and remove every inverse-occurrence dipole
target: leavitt-three-gate-kernel-picture-has-area-at-least-six
requires:
  - leavitt-length-six-three-gate-weight-survivor
---

Each relator vertex has three `z`-arcs.  A coefficient-boundary picture pairs
all of them with oppositely oriented arcs, so its number of vertices is even.
The first possible areas are therefore two and four.

Use the cyclic forms

```text
R_0 ~ z h_1 z h_2 z^(-1) h_0,
R_1 ~ z k_1 z k_2 z^(-1) k_0.
```

The artifact enumerates:

1. the choice `R_0^(+-1),R_1^(+-1)` at every vertex;
2. every pairing of positive `z`-legs with negative `z`-legs;
3. connected pairings whose induced ribbon surface has genus zero;
4. the coefficient-region cycles of the ribbon permutation.

It rejects a pairing whenever an arc joins occurrence `i` of `R_j` to the
inverse occurrence `2-i` of `R_j^(-1)`, since those two vertices form an
immediate picture dipole.  Region labels are reduced exactly in

```text
U=C_2(h_0)*Z(h_1)*C_2(h_2)*C_2(k_0)*Z(k_1)*Z(k_2).
```

A disk candidate may choose any one region as the outer region; every other
region must have identity label.  Exhaustion returns no such reduced pairing
at area two or four.

Before the dipole test, apparent candidates do occur.  At area two they are
the complete gluing of a relator to its inverse.  At area four they are
composites of the same inverse-cell cancellations, with degree-two and
degree-four regions made from the square gates.  Every one contains a matched
inverse-occurrence arc and disappears under reduction.  Thus the failure of
the global weight test does not itself create a low-area kernel: its first
curvature patterns are reducible dipole assemblies.

This is deliberately a universal-square statement.  It does not rule out an
area-four picture whose internal region uses a special relation among the
actual Leavitt corner labels.  It isolates the next finite task exactly:
enumerate actual coefficient-region identities occurring in the four-cell
ribbon types, or move to the first genuinely three-gate area, six.

