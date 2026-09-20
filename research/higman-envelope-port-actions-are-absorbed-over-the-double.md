---
rg: 2
id: higman-envelope-port-actions-are-absorbed-over-the-double
kind: claim
title: In any action of a Higman–Clapham envelope with finitely generated stabilizers, all but finitely many base orbits in each orbit are absorbed into the double F *_N F′, and the input acts freely on them; if no base orbit is absorbed, a finite-index subgroup of the input embeds in a finite product of normalizer sections N(Q)/Q of the double
distinct_from:
  permutational-ports-need-stabilizers-crossing-every-splitting: that shows type (A) and port stabilizers must be hyperbolic on the envelope's tree; this describes the whole shape of any action of the envelope with finitely generated stabilizers, which both criteria require.
  higman-clapham-envelopes-are-hnn-over-machine-times-input: that builds the envelope and transfers decidability; this classifies the permutation structure an envelope action must have.
  amalgams-of-orbit-finite-actions-are-type-a2: that computes stabilizers of amalgam actions from orbit-finite edge groups; this is the converse analysis for one HNN, where edge groups need not be orbit-finite.
---

## Proposed dependency record (not an accepted route)

The following rejected claim-level metadata is preserved verbatim as a
proposed dependency record. It is not a compiled route, does not establish
this claim, and requires individual mathematical review before any route
is accepted. The historical mathematical prose below is unchanged.

```yaml
requires:
  - higman-clapham-envelopes-are-hnn-over-machine-times-input
  - permutational-ports-need-stabilizers-crossing-every-splitting
  - cofinite-abelian-subgroups-give-relative-pbh
```

**ESTABLISHED** (lane bh-ra-counter, 2026-09-19; elementary Bass–Serre theory; not reviewed; no
priority claimed). It is progress on SYNTHESIS v8 gate #4, a type (A) overgroup of Osajda's group,
and it neither builds that overgroup nor obstructs it.

## Setting

As in `higman-clapham-envelopes-are-hnn-over-machine-times-input`, §1:
- `G = F/N`, with benign pair `(K, L)`, and `H = HNN_t(K, L)`, with `t` centralizing `L`;
- `M_2 = ⟨F, F′⟩ × 1 ≅ F *_N F′`, which we call the **double**;
- `M_1 = {(m, π(m))}`, the graph of `π : F *_N F′ → G`, and `φ : M_2 → M_1` the isomorphism;
- `B = H × G`, and the envelope `P = HNN_s(B, M_2 →φ M_1)`.

`P` acts on a set `S`, with every point stabilizer `P_x` finitely generated. Both permutational
criteria require this: type (A), and Houghton ports (`cofinite-abelian-subgroups-give-relative-pbh`).

## Theorem

1. **σ-equation.** Actions of `P` on `S` correspond exactly to pairs `(B ↷ S, σ ∈ Sym(S))` with
   `σ^(-1) m σ = φ(m)` on `S` for all `m ∈ M_2`, via `σ = s`. So `σ` is an isomorphism of
   `M_2`-sets from `S` to `φ^*(S|_(M_1))`.
2. **Graph of the stabilizer.** For `x ∈ S`, `P_x` is the fundamental group of a graph of groups
   `𝒴_x` with:
   - vertices: the `B`-orbits in `P·x`, with vertex groups the `B`-stabilizers;
   - edges: the `M_2`-orbits in `P·x`. The edge at `q` joins `B·q` to `B·s^(-1)q`. Its group is
     `(M_2)_q`, included in `B_q`, and it maps onto `(M_1)_(s^(-1)q) ≤ B_(s^(-1)q)` by conjugation
     by `s`.
3. **Absorption.** There is a finite connected subgraph `𝒴_0 ⊆ 𝒴_x` such that:
   - `𝒴_x \ 𝒴_0` is a forest;
   - every vertex `v` outside `𝒴_0` has, at a suitable representative `q`, vertex group equal to the
     edge group of its edge toward `𝒴_0`. That is, `B_q = (M_2)_q` or `B_q = (M_1)_q`.
4. **The input is free off the core.** On every `B`-orbit outside `𝒴_0`, the stabilizers of
   `G = 1 × G` are trivial. So in each `P`-orbit, `G` acts freely on all but finitely many `B`-orbits.
   On those orbits the `B`-stabilizers lie in conjugates of the double `M_2`, or of its twisted copy
   `M_1`.
5. **No absorption.** Suppose every `𝒴_x` is finite and `P` has finitely many orbits, which is the
   case of a type (A) action with a finite quotient graph.
   - Then `M_2` has finitely many orbits `M_2/Q_1, …, M_2/Q_r` on `S`.
   - Some finite-index `G_0 ≤ G` embeds in `∏_i N_(M_2)(Q_i)/Q_i`.
   - The model case is `Q = ker π`, where `M_2/ker π ≅ G`.
6. **With c6514e7e6e.** In a type (A) or port action, `P_x` contains an element hyperbolic on the
   tree of `P`. So `𝒴_0` is not a single vertex group: either it has a cycle, or some edge group is
   proper at both ends.

## Proof

1. The universal property of HNN extensions. ∎
2. Standard Bass–Serre theory, as in the stabilizer step of
   `amalgams-of-orbit-finite-actions-are-type-a2`.
   - `P_x\P/B` corresponds to the `B`-orbits in `P·x`, and `P_x\P/M_2` to the `M_2`-orbits.
   - `m ∈ (M_2)_q` iff `s^(-1)ms` fixes `s^(-1)q`, and `s^(-1)ms = φ(m) ∈ M_1`. ∎
3. `π_1(𝒴_x)` is the direct limit of `π_1` over finite connected subgraphs. Finitely many generators
   lie in one of them, `𝒴_0`, so `π_1(𝒴_0) → π_1(𝒴_x)` is onto. It is injective, since
   subgraphs of groups inject.
   - For any finite connected `𝒴_1 ⊇ 𝒴_0`, the map `π_1(𝒴_0) → π_1(𝒴_1)` is then an isomorphism.
   - An extra edge closing a cycle adds a stable letter, and normal forms show it is new.
   - Attaching a leaf `v` along `e` gives `A *_(G_e) G_v`, which equals `A` iff `α_e(G_e) = G_v`, by
     the amalgam normal form.
   - Induct outward. ∎
4. `G` is normal in `B`, and `G ∩ M_2 = 1 = G ∩ M_1`, since the first coordinate of `M_1` is
   injective. For `q` as in item 3 and `b ∈ B`,
   `G ∩ B_(bq) = b(G ∩ B_q)b^(-1) ⊆ b(G ∩ M_j)b^(-1) = 1`. ∎
5. `M_2`-orbits are the edges, and there are finitely many.
   - `G` centralizes `M_2 ≤ H × 1`, so it permutes the `M_2`-orbits. A finite-index `G_0` fixes each
     one.
   - `G_0` acts on `M_2/Q_i` by `M_2`-equivariant permutations, which form `N(Q_i)/Q_i` acting on the
     right. Faithfulness on `S` gives the embedding.
   - `ker π` is normal in `M_2`, with quotient `G`. ∎
6. Item 3 of `permutational-ports-need-stabilizers-crossing-every-splitting`. A graph of groups with
   no cycle, all of whose edge groups are onto one side, has `π_1` equal to a vertex group, which is
   elliptic. ∎

## What this says about gate #4

A type (A) overgroup built on the envelope has to look like this:
- a finite core of base orbits, which carries the pair-orbit finiteness and the stabilizers'
  hyperbolic elements;
- trees of absorbed base orbits, whose stabilizers sit inside the double `F *_N F′` and on which
  the input acts freely.

In the unabsorbed case the input is recovered only as `M_2`-automorphisms of cosets of the double.
Those cosets' stabilizers, such as `ker π = ⟨⟨N, F′⟩⟩`, are infinitely generated, while the base
stabilizers stay finitely generated.

The naive actions all fail:
- **Product actions.** Take `X × Y`, with `H` acting on `X` and `G` freely on `Y`. `M_2` is trivial
  on `Y`, so every base orbit contains infinitely many `M_2`-orbits. If a `P`-orbit meets only
  finitely many base orbits, `𝒴_x` has finitely many vertices and infinitely many edges, and `P_x`
  has infinite rank. Only absorbed trees could rescue such actions.
- **The coset action `P/G`.** It is elliptic (c6514e7e6e).
- **A base orbit `B/M_1`.** Its `M_2`-orbits map onto `⟨F, F′⟩\H/⟨F, F′⟩` by the first coordinate.
  So with finitely many base orbits it fails as soon as that double coset space is infinite.

**Status of gate #4:** OPEN. No construction and no obstruction. The design target is a `B`-set
satisfying item 1 with a finite or absorbed quotient graph.

## Lesson for general BH

**A permutational Higman embedding must write the relators into the permutation structure.**
- In the Higman–Clapham envelope, the only place the input `G` can act non-freely, or be recovered
  at all, is on cosets of the double `F *_N F′`, which is where the benign subgroup `N` lives.
- Everything else is either a finite core or absorbed trees on which `G` is free.
- So the pair-orbit finiteness a type (A) action needs must be arranged on the double itself: the
  machine that recognizes `N` has to act on a set with finitely many orbits of pairs.
- That is the permutational form of benignity: `N` must be benign **as a permutation datum**, not
  only as a subgroup.
- Non-exactness does not enter. What costs anything is making Higman's benign-subgroup machinery
  permutationally finite.

Credits: Higman's embedding theorem and benign subgroups (Higman), Clapham's decidability transfer,
the Aanderaa–Cohen modular machines, Bass–Serre theory, and the envelope's HNN form
(bh-invent-14). All are recalled, not re-read at source.
