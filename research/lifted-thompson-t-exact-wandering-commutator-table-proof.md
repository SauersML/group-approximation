---
rg: 2
id: lifted-thompson-t-exact-wandering-commutator-table-proof
kind: route
title: Wandering-interval table in F inside T-bar and a bridge count for shift templates
target: lifted-thompson-t-exact-wandering-commutator-table
requires: []
---

Self-contained.

## 1. Exact table

**Dynamics of `x0`.**  On `(0,1)` we have `x0(t) < t`.  So `x0` has no interior
fixed point.  Moreover `x0` maps `[1/4, 1/2]` onto `[1/8, 1/4]` and
`[1/2, 3/4]` onto `[1/4, 1/2]`.  Hence the intervals `x0^n(J)`, for `n in Z`,
have pairwise disjoint interiors: they are consecutive fundamental domains of
the free action of `<x0>` on `(0,1)`.  All of these maps fix `Z` and commute
with `z`.

**Choice of `c0` and `h0`.**  The elements of `F` supported in the dyadic
interval `J` form a copy of `F`, which is non-abelian.  So we may choose
`c0, h0` there with `y = [c0, h0] != 1`.

**Supports.**  Here "supported in `J`" means the identity off `J + Z`.  So
`c_n` and `h_n` are supported in `x0^n(J) + Z`.

**Off-diagonal entries.**  For `m != n`, the supports of `c_m` and `h_n` meet
at most in endpoints.  Two homeomorphisms with such supports commute, so
`[c_m, h_n] = 1`.

**Diagonal entries.**  `[c_n, h_n] = x0^n [c0, h0] x0^(-n) = a_n y a_n^(-1)`.

**The graph.**  CCC2 is required on every oriented edge `(v,w)` with
`v != w`, and these are exactly the pairs above.  An infinite complete graph
has infinite chromatic number.

**The mark is not central.**  `y` fixes `0`.  If `y = z^k` with `k != 0`, then
`y(0) = k`, a contradiction; and `y != 1` by choice.

## 2. Bridge count

**Reduction.**  Conjugating by `s^(-m)` and freely reducing gives a cyclic
conjugate, which has the same area.  So consider, with `k > 0` (the case
`k < 0` is symmetric), the cyclic word

```text
W = c0 . s^k . h0 . s^(-k) . c0^(-1) . s^k . h0^(-1) . s^(-k).
```

Call its `s`-segments `sigma_1 = s^k`, `sigma_2 = s^(-k)`, `sigma_3 = s^k`
and `sigma_4 = s^(-k)`, in cyclic order.

**The diagram.**  Let `D` be a van Kampen diagram for `W` with `N` cells.
Each boundary occurrence either lies on the boundary of a cell, or lies on an
edge of `D` that belongs to no cell.

- **Cell occurrences.**  A cell has at most `P` edge sides, and each occurrence
  of the first kind occupies a distinct side.  So there are at most `N P` of
  them.
- **Bridge occurrences.**  An edge of the second kind is traversed twice by
  the boundary cycle, once reading `s` and once reading `s^(-1)`.  The
  boundary arc strictly between the two traversals is a closed loop in `D`,
  so its label is trivial in the group.

**Where bridges can land.**  A bridge cannot join two occurrences in segments
of the same sign, since it would read the same letter twice.  The other
pairings between different segments force triviality of an arc:

| pairing          | arc                   | forces           |
|------------------|-----------------------|------------------|
| sigma_1–sigma_2  | `s^a h0 s^(-b)`       | `h0 in <s>`      |
| sigma_3–sigma_4  | `s^a h0^(-1) s^(-b)`  | `h0 in <s>`      |
| sigma_2–sigma_3  | `s^(-a) c0^(-1) s^b`  | `c0 in <s>`      |
| sigma_4–sigma_1  | `s^(-a) c0 s^b`       | `c0 in <s>`      |

Each case is excluded by hypothesis.

**Counting.**  So every one of the `4k` segment letters is either a cell
occurrence or paired with a letter inside the blocks `c0^(+-1)` and
`h0^(+-1)`.  Those blocks contain `2(|c0| + |h0|)` letters in total.  Hence

```text
4k <= N P + 2(|c0| + |h0|).
```

## 3. Literal templates die

**The hypothesis holds in `T̄`.**  Nontrivial powers of `x0` fix no point of
`(0,1)`.  The element `c0` fixes `3/4`, and `c0 != 1`.  So `c0` is not in
`<x0>`, and the same holds for `h0`.

**Bounded edge length gives finite chromatic number.**  If every edge of a
graph on `Z` has length at most `L`, then colouring `n` by `n mod (L+1)` is
proper.  Two vertices of the same colour differ by a nonzero multiple of
`L + 1`, so they are not adjacent.

So on any subgraph with infinite chromatic number, `|m - n|` is unbounded
along edges, and §2 makes the CCC2 area of the literal words unbounded.
