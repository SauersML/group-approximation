---
rg: 2
id: injective-binary-automata-have-formalizable-left-inverses
kind: claim
title: Every injective binary cellular automaton has some left inverse with which it forms a formalizable pair
distinct_from:
  binary-left-inverse-pairs-are-formalizable: that asks formalizability for every left inverse of every pair; this asks it only for some left inverse, which is implied by that claim and already gives the same Kaplansky payoff.
  stable-finiteness-forces-binary-surjunctivity: that is the payoff on hosts with stably finite F_2[G]; this is the host-free mechanism the payoff needs.
artifacts:
  - research/artifacts/formalizability-by-shear-decomposition-2026-09-12.md
---

**OPEN.** For every group `G` and `n >= 1`, every injective automaton `tau` on `(F_2^n)^G` has a
left-inverse automaton `sigma` such that some representatives satisfy `sigma o tau = id` formally.

By `formalizable-left-inverse-iff-clean-shear-dilation`, this is equivalent to: every injective
binary automaton is the restriction to the zero-ancilla subshift of a structurally reversible word
whose ancillas vanish formally.

## Attempts

- **Structurally reversible automata.** True on every group, also after regrouping along a
  finite-index subgroup (`structurally-reversible-automata-are-formalizable`). These are all
  bijective.
- **Decomposition with ancillas.** Functional dilations always exist: two track shears and a swap.
  Formal cleanliness of the ancillas is the claim itself, and the input-erasure step is where the
  defect `X + sigma~(tau~(X))` appears. So circuit decompositions, including Kari-type block
  permutations, only re-express the problem.
- **Finite fields.** Frobenius-equivariant left-inverse extensions exist over every `F_(2^k)`
  (`binary-left-inverse-pairs-extend-over-every-finite-field`). So finite-field points never
  obstruct, and the claim is a uniform-degree statement over infinite fields.
- **Stably finite hosts.** On any host with stably finite `F_2[G]`, the claim fails for every strict
  automaton: formal pairs are bijective there. So a proof must produce Kaplansky failures from
  strict automata, and a strict automaton with no formalizable left inverse must live on a host
  whose group algebras are stably finite, or on one where they aren't but formality still fails.
- **Where it stops.** No mechanism chooses representatives, or equivalently a circuit, with formally
  clean ancillas for an automaton that reads more than one cell and is not structurally reversible.
