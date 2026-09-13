---
rg: 2
id: amenable-infinite-simple-circle-groups-fix-a-point-proof
kind: route
title: Proof that amenable infinite simple groups of circle homeomorphisms fix a point
target: amenable-infinite-simple-circle-groups-fix-a-point
requires: []
---

Let `S` be infinite, simple and amenable, acting on `S^1` through a nontrivial
homomorphism `rho`. Its kernel is a proper normal subgroup, hence trivial, so `rho`
is injective. Write `g x` for `rho(g)(x)`.

1. **Orientation.** The orientation character `S -> Z/2` has a kernel of index at
   most 2. A simple infinite group has no subgroup of index 2, so the character is
   trivial and `S` acts by orientation-preserving homeomorphisms.
2. **Invariant measure.** An amenable group acting continuously on a compact
   metrizable space preserves a Borel probability measure: apply an invariant mean
   to the action on `C(S^1)` and use the Riesz representation theorem. Let `mu` be
   an `S`-invariant probability measure on `S^1`.
3. **Atoms.** Suppose `mu` has an atom. Only finitely many atoms have mass at least
   any given positive number, so the set `A` of atoms of maximal mass is finite,
   nonempty and `S`-invariant. The kernel of `S -> Sym(A)` is a normal subgroup of
   finite index. It is not trivial, since `S` is infinite, so it is all of `S`, and
   `S` fixes every point of `A`.
4. **No atoms: the rotation homomorphism.** Fix `p ∈ S^1` and put
   `h(x) = mu([p, x)) ∈ R/Z`, the mass of the counterclockwise arc from `p` to `x`.
   Because `mu` has no atoms, `h` is continuous and masses of consecutive arcs add
   modulo 1. For `g ∈ S`, orientation preservation sends the arc `[p, x)` onto
   `[gp, gx)`, so modulo 1
   `h(gx) = mu([p, gp)) + mu([gp, gx)) = h(gp) + mu(g[p, x)) = h(gp) + h(x)`.
   Hence `c(g) = h(gp)` satisfies `h ∘ g = h + c(g)`, and `c : S -> R/Z` is a
   homomorphism. An infinite simple group is not abelian, so `c` is trivial and
   `h ∘ g = h` for every `g ∈ S`.
5. **A point whose fibre is a singleton.** The support of `mu` is closed and has no
   isolated point, since an isolated point of the support would be an atom. So it is
   uncountable. Its complement is a disjoint union of countably many open arcs, with
   countably many endpoints. Pick `x` in the support that is not an endpoint of a
   complementary arc. For `y != x`, the open arc `(x, y)` meets the support: if it did
   not, it would lie in a single complementary arc whose closure contains `x`, and
   `x` would be an endpoint of that arc. The same holds for `(y, x)`. Both arcs are
   open and meet the support, so both have positive mass, and
   `h(y) - h(x) = mu([x, y)) ∈ (0, 1)`. Hence `h^{-1}(h(x)) = {x}`, and `h(gx) = h(x)`
   forces `gx = x` for all `g ∈ S`.
6. **Conclusion.** In both cases `S` fixes some point `p'`. The complement
   `S^1 \ {p'}` is an open arc homeomorphic to `R`, and `S` acts on it faithfully by
   orientation-preserving homeomorphisms, because a homeomorphism of the circle that
   fixes `p'` and is the identity off `p'` is the identity.

Contrapositive: if the action of an infinite simple group on the circle has no global
fixed point, the group is non-amenable. ∎
