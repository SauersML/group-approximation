---
rg: 2
id: b8-graph-cone-wall-classes-sparse-cuts-proof
kind: route
title: Carriers of hyperplanes in a graph are closed edges, so the piece-path condition forbids short paths between distinct edges of a class
target: b8-graph-cone-wall-classes-are-sparse-edge-cuts
requires: []
---

**Definitions used.** Quoted from Jankiewicz--Wise, *Cubulating small
cancellation free products*. The text was extracted from the authors' PDF,
dated November 5, 2021; see `research/artifacts/hl-rips-segev-limits-2026-09-14.md`.

- §2.1: "For a hyperplane Ũ of X̃, we let N(Ũ) denote its carrier, which is the
  union of all closed cubes intersecting Ũ. The hyperplanes Ũ and Ṽ osculate
  if N(Ũ) ∩ N(Ṽ) ≠ ∅ but Ũ ∩ Ṽ = ∅." These definitions are applied to the
  cube complex `Y` in the same way.
- §2.3: "A piece-path in Y is a path in a piece of Y."
- Definition 2.3 (1): "The collection of hyperplanes of each Yi are partitioned
  into classes such that no two hyperplanes in the same class cross or
  osculate, and the union U = ∪Uk of the hyperplanes in a class forms a wall in
  the sense that Yi − U is the disjoint union of a left and right halfspace."
- Definition 2.3 (2): "If P is a path that is the concatenation of at most 8
  piece-paths and P starts and ends on the carrier N(U) of a wall then P is
  path-homotopic into N(U)."

**Readings.**
- The halfspaces in (1) are nonempty. As the two parts of a disjoint union,
  each is open and closed in `Y − U`.
- "Path-homotopic into `N(U)`" means homotopic relative to its endpoints to a
  path whose image lies in `N(U)`.

**Proof.** In a graph the cubes are vertices and edges. A hyperplane is the
midpoint `m_e` of an edge `e`, and its carrier `N(m_e)` is the closed edge `e`.
Two distinct hyperplanes never cross.

1. Distinct midpoints are disjoint. So `m_e` and `m_e'` osculate exactly when
   the closed edges `e` and `e'` share a vertex. Condition (1) forbids this
   inside a class, which is item 1.
2. Let `U` also denote the set of midpoints of the edges in the class. By
   condition (1), `Y − U = H ⊔ H'`, where the halfspaces `H` and `H'` are
   nonempty and open and closed in `Y − U`. So each is a union of components of
   `Y − U`.
   - Every component of `Y − U` contains a vertex: each point of an edge `f`,
     other than a midpoint in `U`, is joined inside `f − U` to an endpoint of
     `f`. So both `S = V(Y) ∩ H` and `S' = V(Y) ∩ H'` are nonempty.
   - An edge `f` not in `U` lies in `Y − U` and is connected, so its endpoints
     lie in one component. So every edge joining `S` to `S'` lies in `U`, which
     is item 2.
3. Let `e != e'` lie in `U`, and let `P` be an edge path of length `k` from an
   endpoint `x` of `e` to an endpoint `x'` of `e'`.
   - If `k = 0` then `x = x'` is a common vertex of `e` and `e'`, contradicting
     item 1.
   - Suppose `1 <= k <= 8`. Each edge of `P` is a piece-path by hypothesis, so
     `P` is a concatenation of at most `8` piece-paths. It starts on
     `N(m_e) = e ⊆ N(U)` and ends on `N(m_e') = e' ⊆ N(U)`.
   - By condition (2), `P` is homotopic rel endpoints to a path `Q` with image
     in `N(U)`. By item 1, `N(U)` is a disjoint union of closed edges, and these
     are its path components. The image of `Q` is path-connected and contains
     `x` and `x'`, so `x` and `x'` lie in one closed edge `f` of `U`.
   - `f` and `e` both lie in `U` and contain `x`, so `f = e` by item 1. Likewise
     `f = e'`. So `e = e'`, a contradiction.

   So `k >= 9`, which is item 3. ∎
