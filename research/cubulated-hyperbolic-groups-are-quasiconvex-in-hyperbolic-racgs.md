---
rg: 2
id: cubulated-hyperbolic-groups-are-quasiconvex-in-hyperbolic-racgs
kind: claim
title: Every cocompactly cubulated hyperbolic group is virtually a quasiconvex subgroup of a hyperbolic right-angled Coxeter group
distinct_from:
  quasiconvex-in-hyperbolic-racgs-iff-square-free-typing: that is a proved equivalent form (typed cube complexes) with the necessary square-free-link test; this is the open question itself.
  convex-cores-inherit-greedy-coding-na: that assumes a hyperbolic ambient and reduces Question 1.1 to (IRR) on cores; this asks whether a hyperbolic ambient exists.
  hyperbolic-racgs-are-contracting-rsgs: that settles Question 1.1 inside the class this bridge would transport it from.
---

**OPEN.** The question has been asked in print.

> "However, the Haglund–Wise construction typically yields a quasiconvex embedding of a compact special hyperbolic group
> Γ into a non-hyperbolic right-angled Coxeter group C, and when this occurs we cannot invoke the results in [13] or [14].
> Further, we know of no procedure that replaces C with a hyperbolic Coxeter group (although we do not know of any
> reason such a procedure cannot exist)."
> — Douba, Fléchelles, Weisman, Zhu, *Cubulated hyperbolic groups admit Anosov representations*, arXiv:2309.03695v1,
> §1.2 (Geom. Topol. 29, 2025). Read via the arXiv HTML page.

Credit for posing it goes to them. No priority is claimed here.

## Statement

Let `G` be a hyperbolic group acting properly and cocompactly on a CAT(0) cube complex. Then some finite-index subgroup
of `G` is isomorphic to a quasiconvex subgroup of `W(Δ)` for a finite graph `Δ` with no induced 4-cycle.

## Equivalent form

By `quasiconvex-in-hyperbolic-racgs-iff-square-free-typing`, it is equivalent to ask the following. Some finite-index
`G' ≤ G` acts geometrically, freely on vertices, on some CAT(0) cube complex `Y` carrying a `G'`-invariant typing of its
hyperplanes into a finite square-free graph `Δ`. At every vertex the types must be distinct, and two edges must span a
square exactly when their types are adjacent.

For a fixed C-special cubulation this is the finite problem **(B\*)**: find a cover `X'` and a type map from the crossing
graph `Γ(X')` onto a square-free graph that is a full embedding on every vertex link.

## Known cases

Everything virtually a quasiconvex subgroup of a hyperbolic RACG, tautologically. In particular:
- **Free groups:** `Δ` edgeless.
- **Closed surface groups:** `W(C_5)`.
- **Hyperbolic RACGs and their quasiconvex subgroups.**
- **Right-angled hyperbolic reflection groups** in dimensions 3 and 4, e.g. the right-angled dodecahedron group
  `W(icosahedron graph)`.
- **Closure.** The class is closed under free products, since `W(Δ_1) * W(Δ_2) = W(Δ_1 ⊔ Δ_2)` creates no square, and
  under passing to quasiconvex subgroups.

## First tests

1. **Square-free links (necessary).** A candidate cubulation must have no vertex link containing an induced 4-cycle
   (item 2 of the equivalent-form node). Equivalently, by item 3 there, it has no tight quadrilateral of hyperplanes.
   - Cubical subdivision fails this test as soon as the complex has a square: square barycentres get 4-cycle links.
   - So the test is about *choosing* the cubulation, not refining one.
   - **Test case:** does every closed hyperbolic 3-manifold group (Kahn–Markovic, Bergeron–Wise) have a geometric
     cubulation with square-free links?
2. **(B\*) on the Haglund–Wise ambient.**
   - Every induced square of the universal typing has a diagonal pair that never co-occurs, once links are square-free.
     So each square can be killed on its own by a commutation (M1).
   - The difficulty is global: commutations create new squares, and merges (M2) need neighbour compatibility.
   - This is a finite constraint problem for each finite cover `X'`.
3. **Dimension 2.** Square complexes with vertex links of girth at least 5 are the first case where neither the free-group
   nor the surface solution applies directly. Try building `Δ` of girth 5 that contains all links as induced cycles and
   subgraphs, and a covering-map typing on a suitable finite cover.

## What a proof would give

- **Q1.1, conditionally.** Together with (L) in `convex-cores-inherit-greedy-coding-na`, it gives BBMZ Question 1.1 for
  every cocompactly cubulated hyperbolic group, closed hyperbolic 3-manifold groups included (Agol).
- **DFWZ's Anosov results.** It would put every cubulated hyperbolic group inside the hyperbolic-Coxeter setting of
  their references [13, 14].

## Attempts

1. **2026-09-19 (lane `bh-q11-bridge`): the two suggested constructions, and the reformulation.**
   - **Adding generators cannot kill a square**, since inducedness is decided on the four vertices.
   - **Adding commutations (quotients `W(Δ) → W(Δ + ab)`) keeps `G` convex-cocompact** exactly when `a, b` never
     co-occur at a vertex.
   - **Davis–Januszkiewicz doubling of a RAAG** never yields a hyperbolic ambient.
   - **Subdividing the nerve into a flag no-square complex** (Przytycki–Świątkowski, Januszkiewicz–Świątkowski) changes
     the group and carries no embedding along.
   - What survives is the typing reformulation and the local test above. Neither a proof nor an obstruction was found.
