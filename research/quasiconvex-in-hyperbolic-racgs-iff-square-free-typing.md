---
rg: 2
id: quasiconvex-in-hyperbolic-racgs-iff-square-free-typing
kind: claim
title: A group is a quasiconvex subgroup of a hyperbolic RACG iff it acts geometrically, freely on vertices, on a CAT(0) cube complex with an invariant hyperplane typing into a finite graph with no induced 4-cycle; so square-free vertex links are necessary, and, keeping the same typing, the only changes of the target graph are commutations or merges of never-co-occurring types
distinct_from:
  cubulated-hyperbolic-groups-are-quasiconvex-in-hyperbolic-racgs: that is the open bridge question; this is an equivalent reformulation of it, with the local necessary condition and the legal moves.
  convex-cores-inherit-greedy-coding-na: that passes (NA) to convex cores inside a given ambient; this characterizes when a hyperbolic ambient RACG exists at all.
  hyperbolic-racgs-are-contracting-rsgs: that is Question 1.1 for hyperbolic RACGs; this describes which groups sit quasiconvexly inside them.
---

**ESTABLISHED** by `quasiconvex-in-hyperbolic-racgs-iff-square-free-typing-proof` (lane `bh-q11-bridge`, 2026-09-19;
elementary lane proof; no priority claimed, and items 1–3 are plausibly folklore). **Referee PASS** (bh-ref-e,
2026-09-19; `research/square-free-typing-criterion-review.md`, landed 93f46a050a). Both directions and items 2–5 were
checked; the three wording repairs are applied here.
Recalled inputs, not re-read at source: Moussong's hyperbolicity criterion, the local-isometry embedding lemma
(Haglund–Wise, *Special cube complexes*, GAFA 2008, §2), Helly for convex subcomplexes, and cores for quasiconvex
subgroups (Haglund 2008; Sageev–Wise 2015).

## Definitions

- `Δ` is a finite simplicial graph, `W(Δ)` its right-angled Coxeter group, and `Σ(Δ)` its cubical Davis complex: vertex
  set `W(Δ)`, and one cube for each coset `wW_T` with `T` a clique of `Δ`. Every edge `{w, ws}` has **type** `s`, types
  are constant along hyperplanes, and the link of every vertex is the flag complex `L(Δ)`, via types.
- A **Δ-typing** of a CAT(0) cube complex `Y` is a map `τ : Hyp(Y) → V(Δ)` such that at every vertex `y`:
  - **(T1)** the edges at `y` have pairwise distinct types;
  - **(T2)** two edges at `y` span a square iff their types are adjacent in `Δ`.

  By flagness, `lk(y) → L(Δ)` is then an isomorphism onto a full subcomplex.
- Two types **co-occur** if some vertex of `Y` has edges of both types.

## Statement

1. **Typing criterion.** For a group `G`, the following are equivalent:
   - (i) `G` is isomorphic to a quasiconvex subgroup of a hyperbolic right-angled Coxeter group;
   - (ii) `G` acts properly and cocompactly, freely on vertices, on a CAT(0) cube complex `Y` carrying a `G`-invariant
     `Δ`-typing, for some finite graph `Δ` with no induced 4-cycle.

   In (ii) ⇒ (i), `G` embeds convex-cocompactly in `W(Δ)` itself, via the developing map.
2. **Local obstruction.** Under (ii), every vertex link of `Y` is a full subcomplex of `L(Δ)`, so its 1-skeleton has no
   induced 4-cycle. So a group in (i) has a geometric cubulation, free on vertices, with square-free vertex links.
3. **Tight quadrilaterals are local.** In any CAT(0) cube complex, some vertex link contains an induced 4-cycle iff there
   are hyperplanes `H_1,…,H_4` with `H_i ⋔ H_{i+1}` (indices mod 4), `H_1 ∩ H_3 = ∅ = H_2 ∩ H_4`, and
   `N(H_1) ∩ N(H_3) ≠ ∅ ≠ N(H_2) ∩ N(H_4)`.

   So in the universal typing (types = hyperplanes of `Y`, target = the crossing graph of `Y`), the squares that no
   commutation can kill are exactly the square links of item 2.
4. **Legal moves.** Let `τ` be a `G`-invariant `Δ`-typing of `Y`, and let `a ≠ b` be non-adjacent types that never
   co-occur.
   - **(M1) Commutation.** `τ` is also a `(Δ + ab)`-typing. So `G` stays convex-cocompact in the quotient
     `W(Δ + ab)`.
   - **(M2) Merge.** Suppose also that no type osculating `a` somewhere (co-occurring with `a` and non-adjacent to it)
     is adjacent to `b`, and symmetrically. Then the merged map is a `Δ/(a=b)`-typing.
   - **Adding generators is useless.** An induced 4-cycle stays induced when new vertices are added. So, among
     modifications of `Δ` along the **same** typing `τ`, only (M1) and (M2) can kill a square. Changing the typing or the
     cube complex itself, e.g. passing to a cover or a different cubulation, is not covered by this statement.
5. **The Haglund–Wise typing is the finest.**
   - If `X = Y/G` is C-special (hyperplanes embedded, no self-osculation, no inter-osculation), then the hyperplanes of
     `X` are a valid typing target: `Δ_HW = Γ(X)`, the crossing graph of `X`. This is the Haglund–Wise embedding
     `G ↪ W(Γ(X))`.
   - Every `G`-invariant typing factors through it, as `φ ∘ τ_HW` for a type map `φ : V(Γ(X)) → V(Δ)` that is a full
     embedding on every link. So the bridge for a given cubulation is the problem
     > **(B\*)** Find a finite cover `X'` and a type map `φ` from `Γ(X')` onto a square-free `Δ` that is a full embedding on
     > every vertex link of `X'`.

     For each **fixed** finite cover `X'` this is a finite search. Over all finite covers it is not.
   - Davis–Januszkiewicz doubling cannot help. It puts `A(Γ)` at finite index in some `W(Γ')`, and `A(Γ)` contains `Z²`
     as soon as `Γ` has an edge, so `W(Γ')` is not hyperbolic.

## Examples

- **Free groups:** type edges of a finite loop-free graph properly with pairwise non-adjacent colors, i.e. `Δ` edgeless.
- **Surface groups:** type the `{4,5}` tiling by the pentagon `C_5`. This is the standard `W(C_5)` embedding.
- **The Douba–Fléchelles–Weisman–Zhu remark (arXiv:2309.03695, §2.2.2).** `C_X` can be non-hyperbolic even when
  `G` is itself a hyperbolic RACG acting on its Davis complex. In item 5's language: `Γ(X)` for a torsion-free
  `X = Σ(Δ)/W'` has induced squares, and merging hyperplane classes of the same `Δ`-type (M2) recovers `Δ`.

## Consequence for BH

- **Bridge.** `cubulated-hyperbolic-groups-are-quasiconvex-in-hyperbolic-racgs` is equivalent to: every cubulated
  hyperbolic group has, virtually, a cubulation with a square-free typing. Item 2 is the first test a candidate
  cubulation must pass.
- **(L) is now about typed complexes.** The Q1.1 route (`convex-cores-inherit-greedy-coding-na`) needs its local lemma
  (L) only for the typed complex `Y` of (ii), which may be any `G`-cocompact convex subcomplex of `Σ(Δ)`.
