---
rg: 2
id: thompson-f-staircase-sets-have-stubborn-layers
kind: claim
title: The first stubborn layer of the staircase monomial set X_m..X_(m+d-1) of the positive monoid of F is given by 2a+1 = 3^(d-1)(2m+1), so no staircase set admits a private pivot order
distinct_from:
  thompson-f-p22-monomials-admit-no-private-pivot-order: that is the single case (m,d) = (2,2), proved by exhibiting the core at a = 7; this is the law for the whole two-parameter family, of which only d = 1 is proved.
  thompson-f-generator-sets-admit-no-private-pivot-order: that proves the d = 1 row, a_min(X_m) = m, by an explicit two-block stubborn set; this conjectures the rows d >= 2, where the cores are provably not block sets.
  thompson-f-stubborn-sets-split-off-the-tail: that is the reduction making each entry of the table a finite parameter-free computation, and it proves the relation a_min(S(0,d)) = a_min(S(1,d-1)) that the law encodes; this is the law itself.
  thompson-f-monomial-doubling-ratio-is-a-finite-computation: that is about the expansion ratio Lambda_S(D), a coarser invariant with a different (and for S_(3,5) still unbounded) growth.
  thompson-f-monomial-sets-all-have-stubborn-layers: that is the qualitative statement for every finite S, supported by an exhaustive small census; this is the exact law on the staircase family, whose divisibility that census shows is not shared by general sets.
artifacts:
  - experiments/thompson-f-pivot-orders-2026-09-18/README.md
  - experiments/thompson-f-pivot-orders-2026-09-18/prefix_core.cpp
  - experiments/thompson-f-pivot-orders-2026-09-18/prefix_census.py
  - experiments/thompson-f-pivot-orders-2026-09-18/law_test.py
  - experiments/thompson-f-pivot-orders-2026-09-18/family.jsonl
  - experiments/thompson-f-pivot-orders-2026-09-18/law_test.jsonl
  - experiments/thompson-f-pivot-orders-2026-09-18/survivors.jsonl
  - experiments/thompson-f-pivot-orders-2026-09-18/core_atoms.py
  - experiments/thompson-f-pivot-orders-2026-09-18/core_atoms.json
---

**OPEN.** Notation as in `thompson-f-stubborn-sets-split-off-the-tail`. For `m >= 0` and `d >= 1` let

    S(m, d) = X_m X_(m+1) ... X_(m+d-1)
            = { x_(i_1) ... x_(i_d) ∈ M : i_1 <= ... <= i_d,  i_t <= m + t - 1 },

the *staircase* sets, where `X_k = {x_0, ..., x_k}`. In the notation used elsewhere in this graph,
`S(m,1) = X_m` and `S(m,2) = S_(m+1, m+3)`: so `S(1,2) = S_(2,4)`, `S(2,2) = S_(3,5)` (the monomial
set behind Guba's `P_(2,2)`), `S(3,2) = S_(4,6)`, and
`S(2,3) = {x_a x_b x_c : a <= 2, b <= 3, c <= 4}` is the set the published census recorded as having
no stubborn layer through `D = 10`.

Let `a_min(m,d)` be the least `a` with a stubborn subset of `M_a` for `S(m,d)`, i.e. the least `a`
with `core(P_a) ≠ ∅` (`thompson-f-stubborn-sets-split-off-the-tail`, item 2).

**Conjecture.**

        2 a_min(m, d) + 1  =  3^(d-1) (2m + 1),      i.e.   a_min(m,d) = 3^(d-1) m + (3^(d-1) - 1)/2.

In particular `a_min` is finite for every `(m,d)`, so **no staircase set admits a private pivot
order**, and the triangular doubling certificate of
`thompson-f-private-pivot-orders-give-doubling-and-non-ore-pairs` has no instance anywhere in this
family.

**Evidence.** Every entry below is an exact peeling computation on the prefix world `P_a`, with the
survivor set re-verified from scratch (`verified_stubborn: true` on every row) and, in the small
cases, against an independent Python implementation.

| `d` | `m` | predicted `a_min` | computed | `core(P_(a_min))` | status |
|---|---|---|---|---|---|
| 1 | 1..6 | `m` | `m` | 2, 8, 40, 221, 1288, 7752 | **proved**: existence by `thompson-f-generator-sets-admit-no-private-pivot-order`, emptiness below `m` by `thompson-f-stubborn-sets-split-off-the-tail`, item 3 |
| 2 | 0 | 1 | 1 | 2 | computed |
| 2 | 1 | 4 | 4 | 24 | computed (published) |
| 2 | 2 | 7 | 7 | 1092 | computed (published, `P_(2,2)`) |
| 2 | 3 | 10 | 10 | 81224 | computed (published) |
| 2 | 4 | 13 | 13 | 7470184 | computed: empty at `a = 12` (`|P_12| = 31 865 925`), nonempty at `a = 13` (`|P_13| = 121 580 760`) |
| 3 | 0 | 4 | 4 | 24 | computed; forced to equal the `(1,2)` row by `thompson-f-stubborn-sets-split-off-the-tail`, item 5 |
| 3 | 1 | 13 | 13 | 134160 | computed: empty for `a <= 12`, nonempty at `a = 13` (`|P_13| = 33 266 625`) |
| 3 | 2 | 22 | empty for `a <= 12` | — | out of reach (`|P_22| = f(28,6) ≈ 1.06 · 10^13`) |
| 4 | 0 | 13 | 13 | 134160 | computed; equals the `(1,3)` row exactly, including `|S · core| = 818220`, as item 5 forces |

Two rows are sharp tests, both predicted before being computed and both requiring the computation to
fail at `a_min − 1` and succeed at `a_min`.
- `(1,3)`: predicted from the rows with `d <= 2` and the single row `(0,3)`. `core(P_12) = ∅` on
  8 947 575 points, `core(P_13) = 134160` on 33 266 625 points.
- `(4,2)`: the next point of the `d = 2` row, at a layer an order of magnitude larger than anything
  the published census reached. `core(P_12) = ∅` on 31 865 925 points, and
  `core(P_13) = 7 470 184` on **121 580 760** points, with `|S · core| = 60 260 012`.

The `(0,4)` row is an independent check of item 5 of
`thompson-f-stubborn-sets-split-off-the-tail` at a 33-million-point layer: it reproduces the `(1,3)`
row exactly, core size and image size alike.

**Consequences if true.**
1. *The one named survivor of the pivot-order obstruction is not a survivor.*
   `thompson-f-is-not-amenable` records, under "Private pivot orders", that
   `{x_a x_b x_c : a <= 2, b <= 3, c <= 4} = S(2,3)` has no stubborn layer through `D = 10` and so
   survives. The law predicts `a_min = 22`. The census's reach (now `D = 12`, `|P_12| = 17 298 645`)
   is ten layers short of the prediction, and every other row of the table was likewise empty until
   exactly its predicted layer. So the survival is an artefact of depth, not a property of `S(2,3)`.
2. *The order-based (triangular) doubling certificate is dead on the whole Guba family.* What would
   survive are doubling certificates that are not orders — Hall-type 2-to-1 matchings not induced by
   an order, flows — and possibly monomial sets outside the staircase family.
3. The growth `a_min ~ 3^(d-1) m` says the obstruction is *not* visible at any fixed depth as the
   degree grows: for every `A` there is a staircase set whose first `A` layers are stubborn-free, and
   such a set then has `Λ_S(D) >= 2` for every `D <= A`, i.e. it doubles every finite subset of
   `⋃_(D <= A) M_D` (item 3 of `thompson-f-p22-monomials-admit-no-private-pivot-order` inside the
   window, moved to the whole layer by item 1 of
   `thompson-f-monomial-doubling-ratio-is-a-finite-computation`; this is the re-derivation recorded
   as item 4 of `thompson-f-stubborn-sets-split-off-the-tail`, which the 2026-09-18 referee pass
   showed is *equivalent* to `Λ_S(D) >= 2` rather than stronger, and which reaches strictly fewer
   layers than the exact `Λ` computation does). So finite doubling windows of any prescribed length
   exist inside this family and are *not* evidence for a pivot order.

**Why `2a + 1`, and what shape the gadget should have.** A binary tree with `a` carets has exactly
`2a + 1` nodes, so the law says

    (nodes of a tree with a_min(m,d) carets) = 3^(d-1) · (nodes of a tree with m carets),

and the degree step `d ↦ d+1` is exactly `a ↦ 3a + 1`, which is the caret count of the **ternary
blow-up**: replace every node of a tree by a caret with two leaves, tripling the node count. So the
gadget a proof needs is plausibly the `(d−1)`-fold ternary blow-up of the degree-one two-block
gadget of `thompson-f-generator-sets-admit-no-private-pivot-order`, transported along
`S(m, d+1) = S(m,d) · X_(m+d)`. This is arithmetic, not a construction: nothing here says the blown-up
set is stubborn, and the core sizes (2 → 24 → 134160 along `m = 1`) are not blow-ups of each other.

**What is missing.** A construction. For `d = 1` the stubborn set at `a = m` is the explicit
two-block set of `thompson-f-generator-sets-admit-no-private-pivot-order`: forests on `D + m + 2`
leaves with no caret across one cut, where exactly one product crosses the cut. For `d >= 2` the
computed cores are *not* block sets (the `S(1,2)` core contains crossing trees), and the 24-point
`S(1,2)` core is *minimal*: neither any subset of size `<= 4` nor any one-point deletion is stubborn
(`core_atoms.py`), so it is an atom and not a union of smaller gadgets. The 24-point core is
invariant under the mirror symmetry (reverse the root order and mirror every tree), which is a
symmetry of `S(1,2)` as a set of forests; so is the 1092-point `S(2,2)` core. A proof of the law
needs a gadget whose size triples the odd number `2a+1` when the degree goes up by one, which is
what `S(m, d+1) = S(m,d) · X_(m+d)` should supply.

**Falsifiable next step.** Every reachable prediction has now been tested and held. `a_min(2,3) = 22`
is out of reach (`|P_22| ≈ 1.06 · 10^13`), and so are `a_min(1,4) = a_min(0,5) = 40` and
`a_min(5,2) = 16` (`|P_16| = f(24,8) ≈ 1.26 · 10^10`). The next steps are therefore not computations but
either the construction asked for in "What is missing", or a cheaper *certificate* that a given layer
has an empty core — the peeling is a fixed point of a monotone operator, so a dual object (an
ordering witness) should exist and would be far smaller than the layer.

## Attempts

- **Direct construction from the `d = 1` block sets (2026-09-18).** The two-block set of
  `thompson-f-generator-sets-admit-no-private-pivot-order` works because, with `K = m+2` roots,
  `X_m` realises *every* adjacent merge, and exactly one of them crosses a cut placed at a root
  boundary; the non-crossing products keep every peel inside the set, and the crossing one has only
  the obvious peel. Dies at degree `>= 2`: with a root cut at position `c`, the elements of `S(m,d)`
  that cross the cut are all those whose leaf block containing position `c` is nontrivial, and for
  `S(2,2)` with `c = 1` there are already four of them, so the minimum of the block set has four
  candidate private successors instead of one. This is the same obstruction the published claim
  records as "the computed cores are not block sets".
- **Small stubborn gadgets (2026-09-18, `core_atoms.py`).** The 24-point `S(1,2)` core is a *minimal*
  stubborn set: no subset of size `<= 4` is stubborn, and no one-point deletion is stubborn either.
  Its six root-leaf-profile classes `(1,1,1,5), (1,2,1,4), (2,1,1,4), (4,1,1,2), (4,1,2,1),
  (5,1,1,1)` have four points each and are individually as far from stubborn as possible: inside
  its own class every point has **five** private successors, out of `|S| = 5`. So no proof can
  proceed by exhibiting a bounded-size gadget and padding it; the whole core is one object, and the
  gadget a proof needs has size growing like the core (2, 24, 1092, 81224 along `d = 2`).
- **Mirror symmetry (2026-09-18, `core_atoms.py`).** The involution "reverse the root order and
  mirror every tree" is a symmetry of `S(1,2)` and of `S(2,2)` as sets of forests, and it fixes both
  cores setwise. It halves the search but does not by itself produce a gadget, because the core has
  no stubborn orbit: each mirror-paired profile class is non-stubborn.
