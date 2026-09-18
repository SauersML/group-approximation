---
rg: 2
id: pgl-n-q-acts-on-rational-polyhedral-cantor-set-proof
kind: route
title: Rational arrangements form a countable atomless algebra, and an element fixing every rational region fixes every rational point
target: pgl-n-q-acts-on-rational-polyhedral-cantor-set
requires:
  - gl-n-q-targets-are-cofinal-in-n
---

Notation as in the target. Chambers of an arrangement of `k >= 1` projective hyperplanes
lie in an affine chart and are open convex polyhedra there; for `k = 0` the only chamber
is `RP^(n-1)`.

**Item 1.**
- *Subalgebra.* Given two rational regions, pass to the union of their arrangements.
  Both are then unions of chambers of one rational arrangement, up to boundaries. Meet
  (intersection), join (interior of closure of union) and complement (interior of the
  complement) are again unions of chambers of that arrangement. So `𝔅_n` is a subalgebra
  of the regular open algebra, with top `RP^(n-1)` and bottom `∅`.
- *Countable.* There are countably many finite rational arrangements, each with finitely
  many chambers.
- *Atomless.* A nonempty rational region contains a chamber `C`. Rational hyperplanes are
  dense in the space of hyperplanes, so some rational hyperplane `H` meets the open convex
  set `C`. Then `C − H` has two nonempty components, both rational regions strictly
  below `C`.
- A countable atomless Boolean algebra is unique up to isomorphism, and its Stone space
  is the Cantor set.

**Item 2.**
- *Action.* `g ∈ PGL_n(Q)` maps rational hyperplanes to rational hyperplanes. As a
  homeomorphism of `RP^(n-1)` it commutes with interior and closure, so it maps rational
  regions to rational regions and preserves the Boolean operations. Stone duality turns
  `U ↦ gU` into a homeomorphism of `S_n`, and this is an action.
- *Faithful.* Suppose `gU = U` for every `U ∈ 𝔅_n`. Let `p` be a rational point. In an
  affine chart around `p`, with rational coordinates, the open simplices with rational
  vertices containing `p` form a neighbourhood basis of `p`. Each is a chamber of the
  rational arrangement spanned by its facets. So `g(p)` lies in the closure of each of
  them, and `g(p) = p`. Now `g` fixes every rational point, in particular `n + 1` points in
  general position, so `g` is the identity of `PGL_n(Q)`.
- The embeddings `GL_k(Q) -> PGL_n(Q)` are those of `gl-n-q-targets-are-cofinal-in-n`.

**Item 3.**
- For `n = 2` a rational arrangement is a finite set of points of `P^1(Q)`, and its
  chambers are the open arcs between them. So `𝔅_2` is the algebra of finite unions of
  open arcs with rational endpoints, taken up to endpoints. Its Stone space is the
  standard blow-up that doubles each rational point.
- The homeomorphism `RP^1 -> R/Z` of the cited identification carries `P^1(Q)` onto the
  dyadic points. So it carries `𝔅_2` onto the algebra of finite unions of dyadic arcs,
  whose Stone space is `{0,1}^N` with the usual action of `T <= V`.

**Item 4.**
- *Pieces of V.* Under the identification, an element of `V` restricted to a standard
  dyadic interval is an orientation-preserving affine map onto a standard dyadic interval.
  It respects the midpoint subdivisions. So its conjugate is the orientation-preserving
  map between the two Farey intervals that respects mediant subdivisions. That map is the
  `PSL_2(Z)` element determined by the two endpoints and the mediant. Hence each element
  of `V` is piecewise `PSL_2(Z)` on finitely many rational arcs.
- *Nowhere V.* If `g ∈ PGL_2(Q) − PGL_2(Z)` agreed with such a piece on an open arc, the
  two Möbius maps would coincide, which is a contradiction.
- *Orbits.* `V·√2 ⊆ PSL_2(Z)·√2`. Suppose `(a√2 + b)/(c√2 + d) = 2√2` with
  `ad − bc = 1`. Then `a√2 + b = 4c + 2d√2`, so `a = 2d` and `b = 4c`, and
  `ad − bc = 2d^2 − 4c^2` is even. This is a contradiction. So `2√2 ∉ V·√2`, while
  `x ↦ 2x` maps `√2` to `2√2`. Belk–Hyde–Matucci's Theorem 1.3 asks for `B` and `G` to
  have the same orbits (verbatim in `research/artifacts/gq-gq-lit-hosts.md` §1), so it
  does not apply.
