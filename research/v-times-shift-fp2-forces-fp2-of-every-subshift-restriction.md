---
rg: 2
id: v-times-shift-fp2-forces-fp2-of-every-subshift-restriction
kind: claim
title: "If the alternating full group of V times the full shift is FP_2, then so is its restriction to every subshift, in particular C(C,Z) ⋊ V"
distinct_from:
  v-times-shift-restriction-kernels-are-perfect: That node proves perfect kernels at minimal subshifts; this one uses the same argument at every closed invariant Y to extract necessary conditions for FP_2 of A(G).
---

Notation of `v-times-shift-alternating-group-restrictions-are-simple`.

**Statement.** Suppose `A(G)` is of type FP_2. Then:

1. For every closed shift-invariant `Y ⊆ Σ`, including non-minimal ones, the
   restriction `A(G|_{C×Y})` is of type FP_2.
2. In particular, taking `Y = {0^Z}`, the group `C(C, Z) ⋊ V` is of type FP_2.
   Here `V` acts on locally constant functions `C -> Z` by precomposition.

Proof in `v-times-shift-fp2-forces-fp2-of-every-subshift-restriction-proof`.

Each of these groups is a **necessary condition** for the missing
prerequisite `v-times-shift-alternating-group-is-of-type-fp2`, and each can
fail on its own. Item 2 is the cheapest test: it involves no shift dynamics.

**Remarks** (not part of the statement).

- `C(C, Z) ⋊ V` is perfect. `V` is simple, and in the coinvariants `e = 1_{[0]}`
  satisfies `e = 1_{[00]} + 1_{[01]} = 2e`, because `V` is transitive on proper
  cylinders. So `e = 0`, and abelianization gives no obstruction.
- `C(C, Z)` consists of locally constant functions, not finitely supported
  ones, so it is not a permutational wreath product. The
  Bartholdi–Cornulier–Kochloukova pair-orbit obstruction therefore does not apply
  directly. Whether `C(C, Z) ⋊ V` is FP_2 is not settled here. It resembles the
  Thompson group of a diagonal cloning system, but no citation has been checked.
- Subshifts with finitely many cylinder follower classes should give tests with
  finitely many similarity types, unlike `A(G)` itself (see
  `v-times-shift-groupoid-has-no-finite-similarity-types`). Such tests
  cannot see the infinite-type difficulty.
