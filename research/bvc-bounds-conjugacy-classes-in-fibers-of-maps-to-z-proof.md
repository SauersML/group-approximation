---
rg: 2
id: bvc-bounds-conjugacy-classes-in-fibers-of-maps-to-z-proof
kind: route
title: Transverse witnesses meet each fiber in a coset of a finite group
target: bvc-bounds-conjugacy-classes-in-fibers-of-maps-to-z
requires: []
---

Let `V_1, ..., V_n` witness BVC for `G`, and let `phi: G -> Z`.

1. **Transverse witnesses have finite vertical part.** Suppose `phi(V_i) != 0`. Put
   `F_i = V_i ∩ ker phi`, the kernel of `phi` restricted to `V_i`. Its image in `Z` is
   infinite, so `F_i` has infinite index in `V_i`. In a virtually cyclic group every subgroup
   of infinite index is finite: if `Z_i <= V_i` is infinite cyclic of finite index and
   `H ∩ Z_i != 1`, then `H ∩ Z_i` has finite index in `Z_i`, so `[V_i : H]` is finite. Hence
   `F_i` is finite.
2. **Fibers of transverse witnesses.** For `m != 0` put `S_i(m) = {v in V_i : phi(v) = m}`.
   It is empty or a single coset `v F_i`, so `|S_i(m)| <= |F_i|`. If `phi(V_i) = 0` then
   `S_i(m)` is empty.
3. **Counting classes.** Let `phi(g) = m != 0`. Then `g` has infinite order and `<g>` is
   virtually cyclic, so `x g x^{-1} in V_i` for some `x in G` and some `i`. Since
   `phi(x g x^{-1}) = m`, we get `x g x^{-1} in S_i(m)`. So every conjugacy class inside
   `phi^{-1}(m)` meets the finite set `S(m) = union of the S_i(m)`, which has at most `C`
   elements. Distinct classes are disjoint, so there are at most `C` of them.
4. **Semidirect products.** Let `G = K ⋊_alpha Z` with multiplication
   `(k, j)(k', j') = (k alpha^j(k'), j + j')`, and fix `m >= 1`.
   - Conjugating by `(x, 0)` gives `(x, 0)(g, m)(x^{-1}, 0) = (x g alpha^m(x)^{-1}, m)`,
     which is `alpha^m`-twisted conjugation.
   - Conjugating by `(1, 1)` gives `(alpha(g), m)`.
   - Every element of `G` is `(x, 0)(1, j)`, so the `G`-class of `(g, m)` inside `K × {m}` is
     the union, over `j in Z`, of the twisted classes of `alpha^j(g)`.
   - Taking `x = g^{-1}` shows `g` is `alpha^m`-twisted conjugate to `alpha^m(g)`, because
     `g^{-1} · g · alpha^m(g) = alpha^m(g)`. So those twisted classes depend only on
     `j mod m`, and there are at most `m` of them.

   Hence each of the at most `C` conjugacy classes in `phi^{-1}(m)` contains at most `m`
   twisted classes, and `R(alpha^m) <= m·C`.

The calibration values come from the standard formula: for an automorphism `alpha` of an
abelian group `A`, `R(alpha) = |A/(1 - alpha)A|`. For `A = Z^r` this is `|det(1 - alpha)|`
when nonzero. For `A = Z[1/2]` and `alpha = 2`, `(1 - 2^m)A` has index `2^m - 1`, since
`2^m - 1` is odd.
