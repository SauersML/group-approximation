---
rg: 2
id: subset-stable-marker-flips-are-virtually-formalizable
kind: claim
title: A marker-flip involution whose flip set survives partial flipping is formalizable after regrouping along a finite-index normal subgroup that avoids its window
distinct_from:
  binary-left-inverse-pairs-need-not-be-formalizable: that shows the six-cell marker involution has no formal representatives as a Z-automaton; this shows it is formalizable as a 4Z-automaton, so formalizability depends on the subgroup along which an automaton is regrouped.
  structurally-reversible-automata-are-formalizable: that proves words of gates form formal pairs; this identifies the one-track marker flips that become words of track shears after regrouping.
artifacts:
  - research/artifacts/formalizability-by-shear-decomposition-2026-09-12.md
  - research/artifacts/binary-formalizability-refutation-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

Let `G` be a group, `N` a normal subgroup of finite index, `W ⊂ G \ N` finite, and
`mu: {0,1}^W -> {0,1}`. For `x in {0,1}^G` put `F(x) = {g : mu((x(gw))_(w in W)) = 1}` and
`tau(x) = x + 1_(F(x))`. Suppose `F(x + 1_S) = F(x)` for every `x` and every `S ⊆ F(x)`.

Then `tau` is an involution. Regrouped over `N`, with alphabet `{0,1}^T` for a transversal `T`,
the pair `(tau, tau)` is formalizable as `N`-automata:
- `tau` is the word `tau_(t_k) o ... o tau_(t_1)` in the track shears `tau_t`, where `tau_t` flips
  the cells of `F(x)` in the coset `Nt`;
- the reversed word is a formal inverse.

**Example.** The six-cell marker involution on `{0,1}^Z` of
`binary-left-inverse-pairs-need-not-be-formalizable` has window `W = {±1, ±2, ±3}`, which avoids
`4Z`, and its flip set survives partial flipping.
- So it is the word of four track shears over `4Z`, and `(tau, tau)` is formalizable as a pair of
  `4Z`-automata.
- As a `Z`-automaton it is not formalizable. So formalizability is not invariant under regrouping.
- The formal representatives differ from track to track. They are `4Z`-equivariant and not
  `Z`-equivariant, consistent with `formalizable-binary-pairs-over-biorderable-groups-are-affine`.

Proof: Sections 5.1–5.2 of the first artifact.
