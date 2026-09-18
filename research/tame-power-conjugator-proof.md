---
rg: 2
id: tame-power-conjugator-proof
kind: route
title: The power conjugator permutes the hyperbolic points of a, cannot be periodic near them, and pulls backward orbits into a compact band of a's wandering set; equal hyperbolic sets would make those backward orbits accumulate on both sides at once
target: tame-power-conjugators-have-more-hyperbolic-points
requires:
  - bs-conjugators-of-wandering-maps-have-invariant-compacta
---

Notation as in the target. `X` has no isolated points.

## Step 1. Basic facts about a tame g

(a) `Per(g) = P_g ⊔ F_g`. Periodic points are non-wandering, and every point of `P_g` is
periodic because `g|P_g` has finite order. Points of `F_g` are periodic: `F_g` is finite
and `g(Ω(g)) = Ω(g)`, `g(P_g) = P_g`, so `g` permutes `F_g`.

(b) `int Per(g) = P_g`. A point `f ∈ F_g` with a neighborhood `U ⊆ P_g ∪ F_g` gives the
open set `U \ P_g ⊆ F_g`, a finite open set containing `f`, so `f` is isolated.

(c) `F_g ⊆ cl(W_g)`, and `W_g = ∅` iff `F_g = ∅`. A neighborhood of `f ∈ F_g` missing the
closed set `P_g` and the other points of `F_g` is infinite, so it meets `W_g`. If
`F_g = ∅`, then `W_g = X \ P_g` is compact and `g`-invariant, and properness applied to
`C = W_g` (with `g^n C = C` for all `n`) forces `W_g = ∅`. If `W_g = ∅` then `X = P_g ⊔ F_g`
with `F_g` clopen and finite, so `F_g = ∅`, and `g = g|P_g` has finite order.

(d) **Backward limits.** For `x ∈ W_g` the set `α_g(x)` of accumulation points of
`{g^-n x : n ≥ 1}` is nonempty and lies in `F_g`. It is nonempty by compactness. A point of
`α_g(x)` in `W_g` has a compact neighborhood `C ⊆ W_g` (as `W_g` is open) visited by
infinitely many `g^-n x`, contradicting properness for `C ∪ {x}`. A point of `α_g(x)` in the
open invariant set `P_g` would force some `g^-n x ∈ P_g`, but `W_g` is invariant and disjoint
from `P_g`.

## Step 2. b preserves Ω(a), P_a and F_a

`Ω(a^k) ⊆ Ω(a)` always, and `P_a ∪ F_a = Per(a) ⊆ Ω(a^k)`, so `Ω(a^k) = Ω(a)`. Hence
`b(Ω(a)) = Ω(b a b^-1) = Ω(a^k) = Ω(a)` and `b(W_a) = W_a`.

`b(P_a)` is clopen and contained in `P_a ∪ F_a`. A point `f ∈ F_a ∩ b(P_a)` would have the
open neighborhood `b(P_a) \ P_a ⊆ F_a`, so it would be isolated. Thus `b(P_a) ⊆ P_a`, and
`P_a \ b(P_a)` is open and contained in the finite set `b(F_a)`, hence empty. So
`b(P_a) = P_a` and `b(F_a) = F_a`. In particular `F_a ⊆ Per(b)`.

## Step 3. The band

This is Steps 1--3 of `bs-conjugator-invariant-compactum-proof`, which use only
`b^-1(W_a) ⊆ W_a` (Step 2) and that `a` acts properly and cocompactly on `W_a`. Fix a
compact fundamental domain `D`. There is `M` such that the compact set
`B = ⋃_(|n| ≤ M) a^n D ⊆ W_a` satisfies:

- `b^-1(B) ⊆ B`;
- for every `x ∈ W_a`, `b^-m(x) ∈ B` for all large `m` (the level `|n|` of `x ∈ a^n D`
  strictly decreases under `b^-1` while it exceeds `M`).

Consequences:
- (i) every `b`-periodic point of `W_a` lies in `B` (it recurs to itself under `b^-1`);
- (ii) `α_b(x) ⊆ B ⊆ W_a` for every `x ∈ W_a`.

## Step 4. F_a ⊆ F_b

Let `f ∈ F_a`. By Step 2, `f ∈ Per(b)`. Let `U` be a neighborhood of `f`. Since `f ∉ B`
(as `B ⊆ W_a`), `P_a` and `B` are closed, and `X` has no isolated points, `U \ (P_a ∪ B ∪ F_a)`
is nonempty, and it lies in `W_a \ B`. By (i) its points are not `b`-periodic. So
`f ∉ int Per(b) = P_b` (Step 1(b)), and `f ∈ Per(b) \ P_b = F_b` (Step 1(a)).

## Step 5. F_a ≠ F_b

Suppose `F_a = F_b`. Since `a` has infinite order, `W_a ≠ ∅` and `F_a ≠ ∅` (Step 1(c)).

**`W_a ⊄ Ω(b)`.** Otherwise `W_a ⊆ Ω(b) \ F_b = P_b`, since `W_a ∩ F_a = ∅`. So
`cl(W_a) ⊆ P_b` because `P_b` is closed, and `F_a ⊆ cl(W_a)` by Step 1(c). That gives
`F_b = F_a ⊆ P_b`, contradicting `P_b ∩ F_b = ∅`.

**Contradiction.** Take `y ∈ W_a ∩ W_b`. By Step 1(d) for `b`, `∅ ≠ α_b(y) ⊆ F_b = F_a`.
By Step 3(ii), `α_b(y) ⊆ W_a`. But `F_a ∩ W_a = ∅`.

So `F_a ⊊ F_b`, which is item 1.

## Step 6. Items 2--4

**Item 2.** In an action of `BG_k`, `b = t a t^-1` is conjugate to `a` in `Homeo(X)`, so it
is tame when `a` is, with `|F_b| = |F_a|`. If `a` had infinite order, item 1 would give
`F_a ⊊ F_b`, impossible for finite sets of equal size.

**Item 3.** Suppose every `a_i` is tame and some `a_i` has infinite order. Item 1 for the
pair `(a_i, a_(i+1))` gives `F_(a_i) ⊊ F_(a_(i+1))`. Then `F_(a_(i+1)) ≠ ∅`, so `a_(i+1)`
has infinite order (Step 1(c)), and the same step applies to `(a_(i+1), a_(i+2))`. Going
around the cycle gives `F_(a_i) ⊊ F_(a_(i+1)) ⊊ … ⊊ F_(a_(i+n)) = F_(a_i)`, a contradiction.

**Item 4.** An embedding into `Λ` gives a faithful action in which all elements act
tamely. In `BG_k` the element `a` has infinite order: `BG_k` is the HNN extension of
`BS(1,k) = ⟨a, b | b a b^-1 = a^k⟩` with stable letter `t` conjugating the infinite cyclic
subgroup `⟨a⟩` to the infinite cyclic subgroup `⟨b⟩`, so `BS(1,k)` embeds in it. In `H_n`
for `n ≥ 4` every `a_i` has infinite order (Higman). Item 2 or 3 then gives a
contradiction.
