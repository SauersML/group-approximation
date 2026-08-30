---
rg: 2
id: stw91-finitary-permutation-wreaths-are-selfless
kind: claim
title: Finitary permutation wreaths of linear C*-simple groups are selfless
distinct_from:
  vigdorovich-linear-selflessness: Vigdorovich applies to each finite packet, while the full wreath is nonlinear over every field when the coordinate set is infinite.
  stw91-directed-unions-of-selfless-groups: that is abstract permanence; this theorem constructs a directed packet system and proves the delicate trivial-amenable-radical condition at every finite semidirect stage.
  stw91-countable-free-direct-sum-is-selfless: that is the special case with no permutation group; the present groups contain arbitrary subgroups of the finitary symmetric group acting nontrivially on the coordinate base.
  agkp-acylindrically-hyperbolic-rd-groups-selfless: every element of the full wreath has a non-virtually-cyclic centralizer, so these groups are not acylindrically hyperbolic; no rapid-decay input is used.
  stw99-problem-xci-cstar-simple-selfless: this is a new positive class assembled from linear packets, not a proof for every C*-simple group.
artifacts:
  - research/artifacts/stw91-finitary-permutation-wreath-audit-2026-08-30.md
---

Let `P` be a nontrivial countable linear group with trivial amenable radical,
let `X` be countably infinite, and let

```text
L <= Sym_fin(X)
```

be any group of finitary permutations.  Then the permutational wreath product

```text
W = P^(X) rtimes L
```

has selfless reduced group C*-algebra.  Consequently `W` is C*-simple.

Here `P^(X)` denotes the restricted direct sum.  For linear `P`, triviality
of the amenable radical is equivalent to C*-simplicity, so the hypothesis can
equivalently be phrased as: `P` is a nontrivial countable linear C*-simple
group.

If `L` is nontrivial, this genuinely adds permutation semidirect products to
the direct-sum construction.  Regardless of `L`, the group `W` is nonlinear
over every field and is not acylindrically hyperbolic.  Thus, for example,

```text
SL_3(Z)^(N) rtimes Sym_fin(N)
```

is a concrete positive instance of STW Problem XCI lying outside both the
linear and acylindrically-hyperbolic classes.
