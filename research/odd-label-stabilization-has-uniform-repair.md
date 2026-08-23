---
rg: 2
id: odd-label-stabilization-has-uniform-repair
kind: claim
title: Odd-label stabilization adds only a fixed bottom-reservoir cost to dyadic Iwahori repair
distinct_from:
  mixed-crt-iwahori-repair-is-labeled-pure-dyadic-rounding: that isolates odd-label stabilization as an additional integer Hoffman gate; this closes that gate using the deep one-third gap and the conductor-one trivial reservoir.
  pure-dyadic-clifford-slots-have-a-uniform-one-third-gap: that treats equal-dimensional pure dyadic packets; this pads unequal odd fibers for the estimate and then balances their dimensions globally.
  bounded-dyadic-conductor-iwahori-pairs-have-uniform-repair: that repairs one fixed unlabeled finite diagram; this proves its constant survives arbitrarily many odd labels and arbitrary odd representation degrees.
---

In the mixed CRT decomposition `(MCR3)`, let `w_omega=dim(omega)` and let
`L` be the weighted physical-rank restriction mismatch `(MCR4)`. There is a
universal constant `H_mix<infinity`, independent of

```text
* the number of odd labels;
* all weights w_omega;
* both odd levels; and
* both dyadic depths,
```

such that the two mixed vertex multiplicity families can be changed by
weighted physical rank at most `H_mix L` to satisfy every labeled edge
equation `(MCR5)`, while preserving both original total dimensions.

The proof has three uniform steps.

First, unequal dimensions inside one odd fiber cause no loss of the deep
gap. Pad the smaller dyadic packet abstractly by trivial conductor-zero
summands until its dimension equals the larger one, and apply `(DCS4)`. If
`h_(+,omega),h_(-,omega)` are the two conductor-at-least-two dimensions,
then

```text
w_omega max(h_(+,omega),h_(-,omega))
   <= 3 L_omega.                                       (OLS1)
```

Consequently the total weighted rank of all deep summands on both sides is
at most `6L`. Replace all of them by trivial dyadic representations inside
the same odd label. This costs `O(L)` physical rank and leaves only the
fixed conductor-at-most-one diagram.

Second, balance the dimensions of every odd label. In the bottom diagram
all dyadic irreducibles have dimension at most two and the one-dimensional
trivial representation is available. The edge mismatch pays the fiber
dimension imbalance:

```text
sum_omega w_omega |d_(+,omega)-d_(-,omega)| <= L_bottom. (OLS2)
```

If an imbalance has odd dyadic size and the surplus representation has no
one-dimensional block, replace one two-dimensional block by two trivial
blocks in that same label. Its physical cost `2w_omega` is at most twice
the nonzero imbalance `w_omega|d_+-d_-|`. Now the exact surplus in every
label is a sum of trivial dyadic blocks. Pool the surplus blocks on each
vertex side and relabel both entire pools by the **globally trivial odd
label**. The two pools have the same physical dimension by global dimension
equality. Every old label is reduced on its surplus side to the smaller of
its two dimensions, while the trivial label receives the same added
dimension on both sides. This works even for an odd label which extends to
only one vertex quotient. It makes every label dimension equal at cost
bounded by a fixed multiple of `(OLS2)` and preserves both ambient
dimensions.

Third, apply the fixed conductor-one integer Hoffman repair independently
inside every now-balanced odd label. Multiplication by `w_omega` scales
both the changed rank and the edge residual, so the same finite-diagram
constant works after summing over arbitrarily many labels.

Since `(MCR4)` gives `L=O(epsilon^2 d)`, changing `O(L)` physical rank costs
`O(sqrt(L/d))=O(epsilon)` in normalized Hilbert--Schmidt distance. The
existing uniform Selberg polar alignment then makes the repaired edge
restrictions literally equal. Thus all exact mixed congruence vertex pairs
admit one dimension- and level-independent linear HS repair constant.

This closes the odd-label-stabilized Hoffman gate. It does not exactify an
arbitrary approximate representation of either modular vertex; that is the
separate vertex-stability input in the full Dogon--Vigdorovich question.
