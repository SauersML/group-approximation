---
rg: 2
id: thompson-f-caterpillar-tuples-cannot-certify-p22
kind: claim
title: "Caterpillar and vine skeletons cannot certify P_(2,2): every set of elements whose first five trees are caterpillars has |S_(3,5) Y| >= (13/6)|Y|"
distinct_from:
  thompson-f-p22-cylinder-functional-needs-thin-skeletons: that proposes guessing a thin skeleton family (vine or comb patterns across the five roots) as step (i) toward R < 2; this proves the entrywise-thin version of that guess cannot work, for any size or degree, and measures how far thin classes sit above the generic optimum.
  thompson-f-cardinality-certificates-need-tower-degree: that bounds the degree of any cardinality certificate for large d; this bounds the shape (entry class) of certificates for d = 2 and is degree-free.
  thompson-f-p22-monomials-admit-no-private-pivot-order: that rules out private-pivot orders via a finite stubborn set; this is a lower bound on |S Y| / |Y| over an infinite class of Y by a local discharging rule.
  thompson-f-finite-state-flows-cannot-prove-nonamenability: that kills automaton-computed lower bounds for expansion over all of M; this is a lower bound over a restricted, subexponential class, and it is sharp in kind (it gives exactly 1 for X_1, where vines are optimal).
artifacts:
  - experiments/thompson-f-p22-skeleton-2026-09-17/skeleton.py
  - experiments/thompson-f-p22-skeleton-2026-09-17/types_check.py
---

**ESTABLISHED** by `thompson-f-caterpillar-tuples-cannot-certify-p22-proof` (agent-verified computation plus a
short local argument; not refereed).

## Setting

- `M` is the positive monoid of Thompson's `F`, in the forest model. An element `y` is a sequence of finite binary
  trees `(t_0, t_1, ...)`, all but finitely many trivial. Left multiplication by a monomial of degree `d` adds `d`
  carets on top of the roots.
- `S = S_(3,5)` is the set of nine normal forms `x_i x_j` with `i <= j`, `i <= 2`, `j <= 3`. On forests it acts
  by the nine ways of adding two carets to roots `0..4` so that three roots remain
  (`thompson-f-p22-cylinder-functional-needs-thin-skeletons`, item 1; checked in
  `experiments/thompson-f-p22-2026-09-17/tuples_model.py`).
- `P_(2,2)` has a cardinality certificate iff some finite `Y ⊆ M` has `|S Y| < 2|Y|`
  (`thompson-f-nonamenable-iff-some-monomial-set-doubles`).
- A **caterpillar** is a binary tree in which every caret has at least one leaf child. Left and right **vines**
  (combs) are caterpillars whose internal nodes all lie on the leftmost or on the rightmost branch.

## Statement

1. **Caterpillar heads.** Let `Y ⊆ M` be finite and nonempty, and let the trees `t_0, ..., t_4` of every
   `y ∈ Y` be caterpillars. The tail `t_5, t_6, ...` is arbitrary. Then `|S_(3,5) Y| >= (13/6) |Y|`.
2. **Vine heads.** If `t_0, ..., t_4` are vines, then `|S_(3,5) Y| >= (12/5) |Y|`.
3. **Other sets.** The same local rule proves bounds for the neighbouring `d = 2` sets:

   | set | caterpillar heads | vine heads |
   |---|---|---|
   | `S_(4,6)` (`P_(2,3)`) | `>= 49/18` | `>= 1129/360` |
   | `S_(2,4)` (`P_(2,1)`) | `>= 5/3` | `>= 5/3` |
   | `X_2` | `>= 4/3` | `>= 4/3` |
   | `X_1` | `>= 1` | `>= 1` |

   For `S_(3,5)` and `S_(4,6)` the bound exceeds 2, so neither caterpillar nor vine heads can certify `P_(2,2)` or
   `P_(2,3)`, at any size or degree.

So step (i) of `thompson-f-p22-cylinder-functional-needs-thin-skeletons`, in its entrywise form of vine or comb
patterns across the five roots, is dead. A certificate for `P_(2,2)`, if one exists, must put trees outside the
caterpillar class, i.e. carets with two non-leaf children, into the first five roots.

## Exact values on thin universes (evidence, not part of the proof)

`skeleton.py` computes `ρ(U) = min |S A| / |A|` exactly over all nonempty `A ⊆ U` by parametric min cut, where `U`
is the set of `n`-tuples with `N` carets whose entries lie in a class. Images are computed in full, so every value
is also an upper bound for `h(S)` with an explicit witness. On the full slices it reproduces
`28/5, 9/2, 277/70, 835/231` (`thompson-f-monomial-doubling-ratio-is-a-finite-computation`) and gives
`(N+2)/(N+1)` for `X_1` on vines.

| set | vines | caterpillars | all trees, same `N` |
|---|---|---|---|
| `X_1` | `18/17` (N=16), tends to 1 | `16/15` (N=14), tends to 1 | |
| `X_2` | `1244/625 ≈ 1.9904` (N=50), rising to 2 | `1.756152` (N=12), flat from N=8 | `1.582046` (N=7) |
| `S_(2,4)` | `668/225 ≈ 2.9689` (N=30), rising | `2.512303` (N=12), flat from N=8 | `2.164091` (N=7) |
| `S_(3,5)` | `1213/271 ≈ 4.4760` (N=24), rising | `3.799688` (N=11), flat at 3.79–3.80 from N=6 | `3.065386` (N=7) |

Other restrictions of `S_(3,5)` at `N = 7`:
- Fixing one outer entry to a vine and leaving the rest free gives 3.8210, against 3.0654 for the full slice.
- Vine / free / free / free / vine gives 4.4274.
- Caterpillar / free / free / free / caterpillar gives 3.7429.
- Strahler number at most 2 (with leaf = 0) is indistinguishable from all trees up to `N = 7`, at 3.0658.

**What this changes.** `thompson-f-p22-cylinder-functional-needs-thin-skeletons`, item 5, uses `X_1` to argue that
the optimum is carried by thin skeletons of vanishing mass. That phenomenon does not survive a change of set:
- The vines that are optimal for `X_1` already rise toward 2 for `X_2`, far above the generic cylinder value `151/105`.
- For `S_(2,4)`, where a certificate `< 2` is known (27/14 with 64 generic cells), caterpillars plateau at 2.51.
- In every tested case except `X_1`, restricting the entries to a thin class makes the ratio worse, not better.

So the vanishing-mass families that could carry the optimum of the cylinder functional for `d = 2` must be thin in
some other sense than their entry class, for example through correlations between the five entries. Products of
caterpillar or vine classes are ruled out for `S_(3,5)` by the theorem, and the table suggests the same for the other
thin classes tested.
