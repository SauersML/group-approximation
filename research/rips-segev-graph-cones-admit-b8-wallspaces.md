---
rg: 2
id: rips-segev-graph-cones-admit-b8-wallspaces
kind: claim
title: For large girth, the one-cone cubical presentation of an original Rips--Segev group over the free product of two cyclic groups satisfies C'(1/20) and B(8) after subdivision
distinct_from:
  rips-segev-groups-are-cocompactly-cubulated: that is the cubulation of the group; this is the cubical small cancellation input one route to it needs.
  b8-graph-cone-wall-classes-are-sparse-edge-cuts: that is an established necessary shape of B(8) wall classes on graph cones; this asks for an actual B(8) wallspace on the Rips--Segev relator graphs.
  rips-segev-groups-are-marked-limits-of-special-groups: that asks for special approximations; this is an ingredient of cubulating the group itself.
---

**OPEN.** Let `Φ` be an `8`-regular graph labeled as in Steenbock,
arXiv:1307.0981, Section "Explicit constructions", with coefficients satisfying
the Rips--Segev condition. Let `Γ = Γ_Φ` be its `{a,b}`-reduction. Steenbock
identifies Rips--Segev's original groups with the groups `G(Γ_Φ)`.

Let `X` be the long wedge of two subdivided circles `X_a`, `X_b`, with
fundamental groups `<a>` and `<b>`, and edges `e_1`, `e_2` each subdivided `q`
times (Jankiewicz--Wise, *Cubulating small cancellation free products*,
Construction 4.3). Let `Y` be the graph analogue of Construction 4.3 for `Γ`:

- every vertex `v` of `Γ` incident to edges of both letters is split into two
  vertices: `v_a`, carrying the `a`-edges, and `v_b`, carrying the `b`-edges;
- `v_a` and `v_b` are joined by a copy of `e_1^{-1} e_2`;
- each `a`-edge or `b`-edge is replaced by the corresponding loop of `X_a` or
  `X_b`, opened into a path.

Because `Γ` is reduced, `Y -> X` is a combinatorial immersion. Then
`π_1 <X | Y> = G(Γ)`.

The claim: there are `q` and `g_0` such that, whenever `girth(Φ) > g_0`,
- the cubical presentation `<X | Y>` satisfies `C'(1/20)` for the pieces of
  JW Definition 2.2, with distinct lifts of `Y` counted as giving cone-pieces;
- `Y` carries a wallspace structure satisfying conditions (1)--(3) of JW
  Definition 2.3.

**Why it matters.** Together with
`b8-hyperbolic-cubical-presentations-cocompactly-cubulated` and
`rips-segev-groups-are-hyperbolic`, this gives
`rips-segev-groups-are-cocompactly-cubulated` for these groups. That answers
Steenbock's question for them through `rips-segev-zero-divisor-via-cubulation`.

## Attempts

1. **The classical theorems don't apply as stated.**
   - JW Theorem 6.2 and Martin--Steenbock's main theorem concern finitely many
     relators, and in Construction 4.3 each cone has `π_1 Y = <R>` cyclic.
   - The defining presentation of `G(Γ)` uses the infinite set of cycle labels
     (Steenbock, the definition of `R` in Section "Rips-Segev groups
     revisited"). Its relators "can have long common parts" (Steenbock,
     introduction).
   - No finite subpresentation satisfying `C'_*(1/20)` over `<a> * <b>` is
     known here.
   - JW Theorem 2.4, which the proof of Theorem 6.2 uses, needs every cone to
     deformation retract to a closed geodesic. So for the single graph cone `Y`
     it applies only if `Γ` has rank one.
2. **The `C'(1/20)` half is expected, not proved.**
   - Steenbock proves every graphical piece of `Γ` has free product length at
     most `3` (Lemma `L: maxplength`), and `γ(Γ) ≥ girth(Φ_Γ)` (Lemma
     `L: mincycle`).
   - JW Lemma 6.1 proves the subdivision estimate `C'_*(1/n) ⇒ C'(1/n)` for the
     circle cones of Construction 4.3.
   - The same estimate should give `C'(1/20)` for `Y` once `girth(Φ)` is large
     and `q` is large compared with the exponents in the labels. This hasn't
     been written out here. It also depends on the definitional reading
     recorded in `b8-graph-cone-wall-classes-are-sparse-edge-cuts`.
3. **The `B(8)` wallspace half is the real gap.**
   - If every edge of `Y` is a piece-path, then by
     `b8-graph-cone-wall-classes-are-sparse-edge-cuts` each wall class is an
     edge cut of `Y` whose edges share no vertex and whose endpoints lie at
     distance at least `9` from each other.
   - In particular each vertex has at most one edge in a given class. So on each
     side of the cut, every vertex keeps all but at most one of its edges.
   - A wall structure must also satisfy condition (2) for all concatenations of
     at most `8` piece-paths, not only for single edges, and must be
     `Aut(Y -> X)`-invariant.
   - No such structure on any Rips--Segev graph is known here, and no
     obstruction to one is known.
