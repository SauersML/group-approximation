---
rg: 2
id: rs-strip-tail-transitivity-forces-primitive-transition-matrices
kind: claim
title: The Robertson–Steger transition matrices are never primitive for a type-preserving group, and are primitive for a type-transitive group whenever it acts ergodically on each typed space of tail classes of singular half-strips, in particular for PGL_3 lattices over a characteristic-zero local field
distinct_from:
  robertson-steger-a2-boundary-algebras-are-rank-two-ck: that pins Robertson–Steger's Theorem H(3) and Corollary H(3)+, which give irreducibility of each M_i for PGL_3(K) lattices; this decides primitivity (true exactly when the type-rotation character is onto), with the same ergodicity input, and isolates the one dynamical statement needed for exotic buildings.
  robertson-steger-a2-two-graphs-are-primitive-and-aperiodic: that is the claim for all vertex-free type rotating Ã₂ groups; item 1 here refutes it for type-preserving groups, and items 2–3 prove the corrected form for PGL_3(K) lattices with K of characteristic zero.
artifacts:
  - research/artifacts/gq-bh-bh-groupoid-frontier.md
---

**ESTABLISHED** (lane proof, bh-groupoid 2026-09-18, inline below; not independently
reviewed; no novelty claimed).

## Setting

- `B` is a locally finite thick Ã₂ building of order `q`.
- `Γ` is a group of type rotating automorphisms acting freely on the vertices with finitely
  many orbits. `θ: Γ -> Z/3` is its type-rotation character, `type(γx) = type(x) + θ(γ)`.
- Notation is Robertson–Steger §7 (arXiv:1302.5593, read at source), with `A = Γ\𝔗` the
  classes of type rotating tiles.
- `𝔰 = ⋃_k 𝔭_(k,0)` is the model half-strip. `𝔖_0` is the space of type rotating isometric
  embeddings `s: 𝔰 -> B`, with the topology of pointwise convergence.
- `s_k` is the `k`-th tile of `s`. `s ~ s'` if they agree on every vertex of `𝔰` with first
  coordinate at least some `K`.
- `𝔖 = 𝔖_0/~` is the space of tail classes. It remembers the parametrization: `s` and
  `s(· + (c,0))` are inequivalent for `c ≠ 0`.
- `𝔖^(t) ⊆ 𝔖` is the clopen set of classes with `type(s(0,0)) = t`.

## Statement

1. **Type obstruction.** If `θ = 0`, i.e. `Γ` is type preserving, then `M_1` and `M_2` are
   not primitive: their graphs have period divisible by `3`.
   - So `robertson-steger-a2-two-graphs-are-primitive-and-aperiodic` is false as stated.
     Every torsion-free cocompact lattice in `SL_3(Q_p)` is a counterexample: it is type
     preserving, and acts freely on vertices with finitely many orbits because vertex
     stabilizers are compact.
2. **Criterion.** Let `Γ_0 = ker θ`. Suppose that for each `t`, `Γ_0` acts on `𝔖^(t)` either
   ergodically for a quasi-invariant measure class in which nonempty open sets have
   positive measure, or with a dense orbit. Then:
   - `M_1` is irreducible;
   - its period is `3` if `θ = 0`, and it is primitive if `θ` is onto.
   The same holds for `M_2`, using vertical half-strips.
3. **Linear case.** Let `K` be a local field of characteristic zero and `Γ` a lattice in
   `PGL_3(K)` acting freely on vertices with `θ` onto. Then `M_1` and `M_2` are primitive, and
   `Λ_Γ` is primitive and aperiodic (with `rs-two-graph-aperiodicity-from-h3-and-irreducibility`).
   The explicit type-transitive examples are certified directly in
   `cmsz-rs-two-graphs-of-orders-two-and-three-are-primitive`.

## Proof

**Row and column sums.** Every row and column of `M_1` sums to `q²`.
- A tile `a` has exactly `q²` horizontal successors: `q` choices for the chamber across the
  edge `a(1,0)a(1,1)`, then `q` for the second chamber.
- Each four-chamber gallery obtained has the reduced type of `𝔭_(1,0)` and does not stammer,
  so it lies in an apartment.
- Two successors in one `Γ`-orbit would be related by some `γ` fixing `a(1,0)`, so `γ = 1`.
- Predecessors are counted the same way.

**Complete reducibility.** A nonnegative matrix whose row and column sums all equal `r > 0`
has no edges between distinct strongly connected components.
- Take a component `C` with no incoming edges from outside. Edges leaving vertices of `C`
  number `r|C|`, and so do edges entering `C`, all of which start in `C`.
- So no edge leaves `C`. Remove `C` and induct.

**Item 1.** If `θ = 0`, the base type `a ↦ type(a(0,0)) ∈ Z/3` is well defined on `A`.
- It increases by `1` along every `M_1`-edge, since the model vertex `(1,0)` has type `1`.
  So the graph of `M_1` is 3-partite and cyclic.
- For `M_2`, it increases by `2`.
- All three types occur, because tiles exist at vertices of every type.

**Item 2.**
1. **The invariant.** If `M_1` is not primitive, there are a set `L` with `|L| ≥ 2`, a
   permutation `τ` of `L` and a non-constant `F: A -> L` with `F(b) = τF(a)` whenever
   `M_1(b,a) = 1`:
   - if `M_1` is reducible, take the component label, with `τ = id` (complete reducibility);
   - if it is irreducible of period `d ≥ 2`, take the cyclic class in `Z/d`, with `τ = +1`.
2. **Φ on 𝔖.** Put `Φ(s) = τ^{−k}F(Γs_k)`.
   - It is independent of `k`, since `(s_k, s_{k+1})` is a shape-`(1,0)` word.
   - It is constant on tail classes (compare at a common large `k`).
   - It is `Γ`-invariant.
   - It is continuous, since it depends only on the first tile.
3. **Φ depends only on the base type.** On each `𝔖^(t)`, `Φ` is a `Γ_0`-invariant
   continuous function, so the hypothesis makes it constant, say `c_t`.
   - So `F(a) = c_{type(a(0,0))}` for every tile representing `a`, using that every tile
     starts some half-strip.
4. **θ onto.** Each class `a` contains tiles of all three base types, so
   `c_0 = c_1 = c_2` and `F` is constant. This is a contradiction, so `M_1` is primitive.
5. **θ = 0.** `F` factors through the base type. Two classes with the same base type have
   the same `F`, so there are at most three cyclic classes, and item 1 gives exactly three.
   The reducible case is excluded for the same reason: the base type is a 3-cycle on the
   classes, so the graph is connected. ∎

**Item 3.** Put `G = SL_3(K)`. Let `Γ'` be the pullback to `G` of `Γ_0` intersected with the
image of `G` in `PGL_3(K)`. It is a lattice in `G`, and its image in `Aut(B)` lies in `Γ_0`.
- As in the proof of RS Theorem `H(3)`, `G` acts transitively on the apartments and, inside
  an apartment, on the sectors based at vertices of a given type. So each `𝔖^(t)` is `G/H_t`,
  with `H_t` closed and noncompact (RS compute `H` for `t = 0`; the other types are
  conjugate).
- By Howe–Moore (as in RS), `Γ'` acts ergodically on each `G/H_t` for the `G`-invariant
  measure class, which has full support.
- A `Γ_0`-invariant function is `Γ'`-invariant. So the hypothesis of item 2 holds for
  `Γ_0`, and item 2 applies with `θ` onto. ∎

## What is left for exotic buildings

There is no ambient group, and the hypothesis of item 2 has to be proved geometrically.
- Bader–Caprace–Lécureux, arXiv:1608.06265, Theorem `ergodic` (read at source): for a
  type-preserving cocompact `Γ`, the action on `𝒲/S` is ergodic. Here `𝒲` is their space of
  marked wall trees and `S ≅ Z` is the singular translation group.
- `𝒲/S` forgets the phase. The reducible-case invariant (`τ = id`) is phase-free, so it
  factors through the half-strip at the base edge of a marked wall tree. So BCL should give
  **irreducibility** of `M_1` for every such `Γ`.
  - This is not written out. It still needs a check of their subspace `𝒲 ⊆ 𝒲̃` and of full
    support of their measure class.
- **Primitivity** needs the phase. For `θ` onto, one needs ergodicity of `Γ_0` on `𝒲/S^3`,
  compatibly with types: the phase modulo `d` may be constrained only through the vertex
  type. Equivalently, the singular Cartan flow on `Γ_0\𝒲` has no eigenvalue that is a root of
  unity other than those forced by the three types.
- In BCL's Hopf argument, the obstruction is the phase holonomy of their projectivities of
  the panel tree `T_u`. These have to be lifted to `Aut(Υ)^0`, together with their translation
  part.
- Open.

**Superseded (2026-09-18, later).** The exotic case is settled without ergodicity by
`a2-rs-matrices-irreducible-and-primitive-iff-type-transitive`:
- irreducible always;
- primitive iff `θ ≠ 0`;
- the proof is local, in the vertex links.

Items 1–3 above remain correct, and item 3 is now a special case.
