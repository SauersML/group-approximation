---
rg: 2
id: kl-three-equal-residue-shapes-inject-for-every-loop-order
kind: claim
title: The length-six residue shapes with one light label inject for every loop order when g avoids three short relations with the loops
distinct_from:
  kl-involution-loop-residue-with-interior-light-label-injects: that splits the loop weight one half each and covers only (1,1,g,1) and (1,g,1,1) with involution loops; this puts the whole loop weight on one loop, reaches (1,1,1,g) and (g,1,1,1), and allows every loop order.
  kl-three-coincidence-residue-words-inject-with-room-for-loops: that is a weight test with positive weight on both loops, so it needs 2/k_y + 2/k_x <= 1; this gives one loop weight zero and moves the curvature of that loop's power regions across their arcs, so involution loops and all small orders are allowed.
  kl-length-six-residue-squares-and-fourth-powers-inject: that settles by substitution the sub-cases where g equals a loop coefficient; this is a curvature argument for every g outside three short relations.
  kl-length-six-coincidence-saturated-torsion-residue: that is the open statement for all residue shapes; this settles the four three-equal +++++- shapes outside explicit relations and leaves the two-pair and ++++-- shapes open.
---

Let `G` be any group, `x, y in G` nontrivial of any orders, finite or infinite,
`g in G` with `g != 1`, and

```text
w = t a_1 t a_2 t a_3 t a_4 t y t^(-1) x,
```

where exactly one of `a_1, ..., a_4` equals `g` and the other three equal `1`.

**(a)** Suppose `a_1 = 1`, i.e. the shape is `(1,1,1,g)`, `(1,1,g,1)` or `(1,g,1,1)`, and:
- (X1) `g` is not in `<x>`;
- (X2) `y` is not in `g <x> g^(-1)`;
- (X3) `g` is not in `y <x>` or `y^(-1) <x>`.

**(b)** Suppose `a_4 = 1`, i.e. the shape is `(g,1,1,1)`, `(1,1,g,1)` or `(1,g,1,1)`, and:
- (Y1) `g` is not in `<y>`;
- (Y2) `x` is not in `g^(-1) <y> g`;
- (Y3) `g` is not in `<y> x` or `<y> x^(-1)`.

In either case `G -> (G * <t>)/<<w>>` is injective, and every reduced spherical
picture over `<G, t | w>` is empty. The interior shapes `(1,1,g,1)` and
`(1,g,1,1)` inject when (X1)-(X3) hold or when (Y1)-(Y3) hold.

**Method.** For (a), weight the three heavy corners and the loop `y` by `1`, and
the light corner and the loop `x` by `0`. The only interior regions of positive
curvature are then regions all of whose corners are `x`-corners, with curvature
`2 pi`. Each hands `2 pi / d <= pi` across each of its `d` arcs. The region on
the other side reads a `y`-corner next to the heavy corner `a_1`, so it carries
weight two per transfer, and (X3) rules out a receiver of weight two that takes
one transfer. Part (b) is part (a) for `t -> t^(-1)` applied to `w^(-1)`. See
`kl-three-equal-residue-one-sided-weight-curvature-proof`.

**Involution loops.** Take `x^2 = y^2 = 1`, the case of the Leavitt search. Then
(X1)-(X3) and (Y1)-(Y3) say the same thing:
- `g` is none of `x`, `y`, `y x`;
- `g x g^(-1) != y`.

`kl-length-six-residue-squares-and-fourth-powers-inject` settles:
- `(1,1,1,g)` with `g = x`;
- `(g,1,1,1)` with `g = y`;
- `(1,1,g,1)` with `g = y`;
- `(1,g,1,1)` with `g = x`.

So the involution cases still open are exactly these:

| Shape | Still open with involution loops |
|---|---|
| `(1,1,1,g)` | `g = y`, `g = y x`, or `g x g^(-1) = y` |
| `(g,1,1,1)` | `g = x`, `g = y x`, or `g x g^(-1) = y` |
| `(1,1,g,1)` | `g = x`, `g = y x`, or `g x g^(-1) = y` |
| `(1,g,1,1)` | `g = y`, `g = y x`, or `g x g^(-1) = y` |

The two bullets above are (I1)-(I3) of
`kl-involution-loop-residue-with-interior-light-label-injects`. So for
`(1,1,g,1)` and `(1,g,1,1)` this removes that node's fourth exception
`g^2 x g^(-1) y = 1`. For `(1,1,1,g)` and `(g,1,1,1)` the result is new.

**Other small orders.** Suppose both loop orders are finite and
`2/k_y + 2/k_x > 1`, i.e. one loop has order two, or the orders are `3` and `3`,
`4` or `5`. The weight test of
`kl-three-coincidence-residue-words-inject-with-room-for-loops` gives nothing
there. Each shape stays open only on this set:

| Shape | Still open |
|---|---|
| `(1,1,1,g)` | (X1), (X2) or (X3) fails, and `g != x^(-1)` |
| `(g,1,1,1)` | (Y1), (Y2) or (Y3) fails, and `g != y^(-1)` |
| `(1,1,g,1)` | one of (X1)-(X3) and one of (Y1)-(Y3) fail, and `g != y` |
| `(1,g,1,1)` | one of (X1)-(X3) and one of (Y1)-(Y3) fail, and `g != x` |

The excepted values are the substitution sub-cases.

**Not covered.**
- **The two-pair `+++++-` shapes.** Both loops get weight zero. A transfer from
  an `x`-region brings one heavy corner and a `y`-corner of weight zero, i.e.
  weight one per transfer.
- **The `++++--` shapes.**
  - With weight on `y` only, the receiver of an `x`-region pairs the N-corner with
    `a_1`, with no loop corner between them. In `(1,1,g)` the region reading
    `n a_1 x^(k_x)` is trivial for every `g`, has weight two, and receives `pi`.
  - With weight on `x` only, the receiver pairs `a_3` with the N-corner, and in
    `(1,1,g)` `a_3` is light.
- **The relations in the tables above.**

DERIVATION
kl-three-equal-residue-one-sided-weight-curvature-proof
