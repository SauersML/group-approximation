---
rg: 2
id: type-a-actors-have-no-proper-power-cyclic-edge-splittings-proof
kind: route
title: Edge and vertex groups have finitely many orbits; a finite or proper-power cyclic piece then forces a finite set, and faithfulness forces a finite group
target: type-a-actors-have-no-proper-power-cyclic-edge-splittings
requires:
  - type-a-actors-split-only-over-orbit-finite-edges
---

Let `G`, `X` and `T` be as in the statement. By (2) of
`type-a-actors-split-only-over-orbit-finite-edges`, every vertex stabilizer and
every edge stabilizer has finitely many orbits on `X`. Since `G` acts on `T`
without a fixed vertex, `G` is infinite (Step 0, (F6), of that proof). Since the
action on `X` is faithful, `X` is infinite.

## (a) Finite edges

If `G_e` is finite, every `G_e`-orbit is finite. There are finitely many orbits,
so `X` is finite, a contradiction.

## (b) Proper-power cyclic pieces

Let `<c>` have finite index in a vertex or edge stabilizer `H`, with `c` of
infinite order.

- **Finitely many orbits.** Write `H = ∪_i <c> h_i` over finitely many right
  cosets. Then `Hy = ∪_i <c>(h_i y)`, so every `H`-orbit is a union of at most
  `[H : <c>]` orbits of `<c>`. So `<c>` has finitely many orbits on `X`.
- **Regular orbits.** An orbit of `<c> ≅ Z` has stabilizer `kZ` for some
  `k >= 0`. It is infinite iff `k = 0`, and then it is a regular `Z`-set. Let
  `r(c)` be the number of infinite `<c>`-orbits.
- **Powers.** Let `p != 0`. A regular `<c>`-orbit, as a `<c^p>`-set, is `Z` with
  `Z` acting by translation by `p`, so it splits into `|p|` regular orbits. A
  finite `<c>`-orbit splits into finite `<c^p>`-orbits. So `<c^p>` has finitely
  many orbits, and `r(c^p) = |p| r(c)`.
- **Conjugates.** For `g in G`, the map `y -> gy` sends `<c>`-orbits bijectively
  to `<g c g^-1>`-orbits and preserves their sizes. So `r(g c g^-1) = r(c)`,
  whenever either side has finitely many orbits.
- **Contradiction.** Suppose `g c^p g^-1 = c^q` with `|p| != |q|`. Neither
  exponent is 0: if `p = 0` then `c^q = 1`, so `q = 0` because `c` has infinite
  order, and similarly for `q`. Hence `|q| r(c) = r(c^q) = r(c^p) = |p| r(c)`, so
  `r(c) = 0`. Then `X` is a finite union of finite `<c>`-orbits, so `X` is
  finite, a contradiction.

## Instances

The splittings in the statement are irreducible by Step 8 of
`type-a-actors-split-only-over-orbit-finite-edges-proof`.

- **`BS(m,n)`.** The vertex stabilizer of the base vertex is `<a>`, and
  `t a^m t^-1 = a^n`. The associated subgroups `<a^m>` and `<a^n>` are proper
  because `|m|, |n| >= 2`.
- **`BG`.** In `H = BS(1,2)`, `<a>` and `<b>` are proper because `H` is
  non-abelian (`b a b^-1 = a^2 != a`). Both associated subgroups are infinite
  cyclic, and the edge stabilizers are their conjugates. Take `c = a`, which
  generates an edge stabilizer, and `p = 1`, `q = 2`, using `b a b^-1 = a^2`.
  If the base edge stabilizer is `<b> = t<a>t^-1` instead, take `c = b`, which
  is conjugate to `b^2` by `t b t^-1`.
- **GBS groups.** The vertex groups are infinite cyclic. A modular value `q/p`
  with `|q/p| != 1` comes from some `g` with `g c^p g^-1 = c^q`, for `c` a
  generator of a vertex group; this is the definition of the modular
  homomorphism.
