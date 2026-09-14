---
rg: 2
id: simple-model-small-defect-lef-proof
kind: route
title: Normal closure in at most the model size steps bounds every length from below
target: simple-model-weak-soficity-with-small-defect-is-lef
requires:
  - sofic-groups-are-surjunctive
artifacts:
  - research/artifacts/weak-soficity-surjunctivity-route-2026-09-12.md
---

Theorems B and C of the artifact.

**Length bound.** Fix `k != 1` in the finite simple group `H` and let `S_n` be
the set of products of at most `n` conjugates of `k` and `k^-1`. Each `S_n` is
symmetric and conjugation-closed, the chain increases, and its union is a
subgroup, normal because each term is conjugation-closed, and nontrivial
because it contains `k`. Simplicity makes it `H`. An increasing chain of
subsets of `H` that stabilizes only at `H` reaches `H` within `|H|` steps,
since each strict inclusion adds at least one element. So every `x` in `H` is a
product of at most `|H|` conjugates of `k^{+-1}`, and subadditivity with
conjugation invariance gives `l(x) <= |H| l(k)`. Taking `x = x_0` with
`l(x_0) >= c` yields `l(k) >= c/|H|`.

**Collapse.** Separation gives `l_F(phi_F(g)) >= c` for `g != 1` in `F`, which
supplies the element `x_0` unless `F = {1}`, where the statement is vacuous.
A defect `k = phi_F(a)phi_F(b)phi_F(ab)^-1` satisfies `l_F(k) <= eps_F < c/|H_F|`,
so the length bound forces `k = 1`. Thus `phi_F` is multiplicative on `F`, and
it is injective there because `l_F(phi_F(g)) >= c > 0` for `g != 1`. That is a
local embedding of `F` into a finite group, so `G` is LEF.

**LEF implies sofic, without citation.** Let `H_F` act on itself by left
translation. The composite `F -> H_F -> Sym(H_F)` is multiplicative on `F`,
and by `regular-action-makes-weak-sofic-defects-maximal` every nontrivial image
has normalized Hamming length `1`. So it is a sofic approximation with defect
`0` and separation `1`. Surjunctivity then comes from the prerequisite.
