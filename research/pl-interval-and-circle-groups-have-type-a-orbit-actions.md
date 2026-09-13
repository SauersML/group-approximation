---
rg: 2
id: pl-interval-and-circle-groups-have-type-a-orbit-actions
kind: claim
title: The interval and circle groups F(A,P) and T(A,P) act on A-points with one orbit of pairs and finitely generated stabilizers, so their orbit actions are of type (A) exactly when the groups are finitely presented
distinct_from:
  pl-rearrangement-groups-have-two-transitive-orbit-actions: that is the rearrangement group V(A,P), whose stabilizer argument uses a contracting conjugator; this is the interval group F(A,P), whose stabilizer is a product of two copies of F(A,P), and the circle group T(A,P), whose stabilizer is F(A,P).
  two-transitive-action-reduces-type-a-to-two-clauses: that reduces the type (A) clauses for 2-transitive actions; the interval action here is not 2-transitive, and its pair clause is checked directly.
---

**ESTABLISHED** through `pl-interval-and-circle-groups-type-a-orbit-action-proof`
(elementary; not independently reviewed; no novelty claimed).

## Setting

As in `pl-rearrangement-groups-have-two-transitive-orbit-actions`: `A ⊆ R` a subring,
`P ≤ R_{>0}` a finitely generated group of units of `A`, with **(S)** every positive
element of `A` a finite sum of elements of `P`, and **(R)** `1 = q + q'` with
`q, q' ∈ P`.

- `F(A,P)` is the group of increasing homeomorphisms `f` of `[0,1]` for which there
  are `0 = x_0 < ... < x_n = 1` in `A` with `f(x) = p_i x + c_i` on `[x_{i-1}, x_i]`,
  `p_i ∈ P`, `c_i ∈ A`.
- `T(A,P)` is the subgroup of `V(A,P)` of elements inducing homeomorphisms of the
  circle `[0,1)/(0 ∼ 1)`.

## Statement

1. `F(A,P)` acts faithfully on `A ∩ (0,1)` with one orbit of two-element subsets, and
   each point stabilizer is isomorphic to `F(A,P) × F(A,P)`. So this action is of
   type (A) exactly when `F(A,P)` is finitely presented.
2. `T(A,P)` acts faithfully and 2-transitively on `A ∩ [0,1)`, and the stabilizer of
   `0` is `F(A,P)`. So if `F(A,P)` is finitely generated, this action is of type (A)
   exactly when `T(A,P)` is finitely presented.

In either case every subgroup of the acting group satisfies permutational
Boone--Higman, has solvable word problem, and embeds in a finitely presented simple
group.
