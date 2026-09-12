---
rg: 2
id: marker-involution-is-formalizable-after-regrouping
kind: claim
title: The marker involution on {0,1}^Z is not formalizable over Z but becomes a word of track shears after regrouping along 4Z
distinct_from:
  binary-left-inverse-pairs-need-not-be-formalizable: that shows the marker involution has no formalizable pair with Z-equivariant representatives; this shows the same automaton, regrouped along 4Z, is a word of track shears with a formal inverse, so formalizability is not invariant under regrouping.
  structurally-reversible-automata-are-formalizable: that proves words of track shears, including after regrouping, are formalizable; this identifies the one-track marker involution as such a word after regrouping and records what that means for the stable target.
  injective-binary-automata-are-stably-formalizable: that stabilizes by identity ancilla tracks; this stabilizes by regrouping along a finite-index subgroup, which decides the Z test case but does not exist on hosts without proper finite-index subgroups.
artifacts:
  - research/artifacts/formal-polynomial-strict-pairs-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

Let `tau(x)_i = x_i + m_i(x)` on `{0,1}^Z` with `m_i(x) = [x_(i-3..i+3) = 001*100]`.

**The word.** Regroup along `H = 4Z`, with blocks `(x_(4k), ..., x_(4k+3))`. For `r = 0..3` put
`S_r : x_(4k+r) -> x_(4k+r) + m_(4k+r)(x)` in every block.
- **Each `S_r` is a track shear.** `m_(4k+r)` reads only cells at offsets `±1, ±2, ±3`, none of them
  congruent to `r` mod 4, so `S_r` is an `H`-equivariant formal involution.
- **The word equals `tau`.** Flipping any subset of the marker set changes no marker, since markers
  within distance 3 exclude each other. So `S_3 S_2 S_1 S_0 = tau` on `{0,1}^Z`.
- **Formal inverse.** The reversed word `S_0 S_1 S_2 S_3` is a formal two-sided inverse.

**Consequences.**
- **Not invariant under regrouping.** With `Z`-equivariant representatives the involution is not
  formalizable (`binary-left-inverse-pairs-need-not-be-formalizable`). With `4Z`-equivariant
  representatives it is.
- **Regrouping is a second stabilization with the Kaplansky payoff.** Let `H` have finite index in
  `G`. A strict automaton formalizable over `H` forces `F_2[H]`, hence `F_2[G]`, to be not stably
  finite.
- **It does not reach the target hosts.** Finitely generated simple hosts have no proper
  finite-index subgroups, so there the ancilla-only form
  `injective-binary-automata-are-stably-formalizable` remains the decisive target.

Artifact, Section 6.5.
