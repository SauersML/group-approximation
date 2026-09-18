---
rg: 2
id: boundary-orbit-wreaths-over-tree-groups-are-not-fp
kind: claim
title: A group of tree automorphisms has infinitely many orbits on pairs of any infinite boundary orbit, so lamp wreath products over such orbits are never finitely presented
distinct_from:
  boundary-orbit-cyclic-wreath-has-fp-simple-envelope: that embeds the boundary-orbit wreath of a contracting group in a finitely presented simple group; this shows the wreath product itself is never finitely presented, which is consistent with that node, since it claims only an envelope.
  lamp-digit-modules-give-self-similar-semidirect-products: that makes these wreath products self-similar; this shows self-similarity cannot come with finite presentation for them, so a finitely presented envelope is always needed.
---

**ESTABLISHED** by the proof below (lane bh-free-25, 2026-09-18; elementary, not
reviewed; no novelty claimed).

## Statement

Let `Q` act by automorphisms on a locally finite rooted tree `𝒯`, let `ξ ∈ ∂𝒯` have
infinite orbit `Ω = Q·ξ`, and let `W ≠ 1` be a group.
1. `Q` has infinitely many orbits on `Ω × Ω`.
2. The permutational wreath product `W ≀_Ω Q` is not finitely presented.

## Proof

1. For distinct `η, ζ ∈ ∂𝒯` let `n(η, ζ)` be the length of their longest common
   prefix. Automorphisms of the rooted tree preserve prefixes, so `n` is
   `Q`-invariant. Since `𝒯` is locally finite, `∂𝒯` is compact. So the infinite set
   `Ω` has an accumulation point, and pairs of distinct points of `Ω` realize
   arbitrarily large values of `n`. Each value is a union of orbits, so there are
   infinitely many orbits.
2. Cornulier's theorem, as quoted at source (arXiv:math/0509090, via the Attempt 1
   record of `every-decidable-group-embeds-in-an-isolated-group`), says: for `W ≠ 1`
   and a transitive `Q`-set `X = Q/H`, the wreath product `W ≀_X Q` is finitely
   presented only if `Q` has finitely many orbits on `X × X`. Apply 1 with `X = Ω`. ∎

## Consequences

- Hosts of the form `W ≀_{Q·ξ} Q` with `Q` acting on a tree (self-similar groups,
  automaton groups, residually finite groups realized on their coset trees) are never
  finitely presented once the orbit is infinite. To use Zaremsky's theorem
  (`fp-self-similar-groups-embed-in-fp-simple-groups`), such a wreath product has to
  be placed inside a further finitely presented self-similar group. It cannot serve
  as its own finitely presented input.
- More generally, the restriction of an action by tree automorphisms to an infinite
  orbit of boundary points never has finitely many orbits on pairs. Vertex orbits are
  finite, because automorphisms preserve depth. So oligomorphic or type (A) actions
  never arise directly from such actions.
