---
rg: 2
id: binary-left-inverse-pairs-need-not-be-formalizable
kind: claim
title: A reversible binary marker automaton over the integers admits no formalizing representatives
invalidates: [formalizable-pairs-reduce-surjunctivity-to-kaplansky, formalizable-left-inverses-reduce-surjunctivity-to-kaplansky]
distinct_from:
  binary-left-inverse-pairs-are-formalizable: that is the universal formalizability claim; this is its negation, witnessed over the integers with alphabet F_2.
  injective-binary-automata-have-formalizable-left-inverses: that asks for some formalizable left inverse of each injective automaton; this refutes it too, because the witness is bijective and its left inverse is unique.
  multilinear-collapse-defect-does-not-obstruct-bijectivity: that shows canonical representatives of a formalizable sitewise pair can fail to be formal; this exhibits a pair for which every choice of representatives fails.
artifacts:
  - research/artifacts/binary-formalizability-refutation-2026-09-12.md
---

**The automaton.** On `{0,1}^Z`, flip cell `i` exactly when
`(x_(i−3), x_(i−2), x_(i−1), x_(i+1), x_(i+2), x_(i+3)) = (0, 0, 1, 1, 0, 0)`. Call the result
`tau`.

**Properties.**
- `tau` is an involution. Markers within distance 3 exclude each other, so the flip set is invariant.
- `tau` is not a translation composed with a complement. It fixes the configuration with a single `1`
  and is not the identity.

**Consequences.**
- **No formalizing representatives.** By
  `formalizable-binary-pairs-over-biorderable-groups-are-affine` with `G = Z`, the left-inverse pair
  `(tau, tau)` has no representatives in which `tau o tau = id` holds formally, on any memories.
  `tau` is bijective, so `tau` is its only left inverse as a function.
- **Two claims are refuted:**
  - `binary-left-inverse-pairs-are-formalizable`, since not every left-inverse pair is formalizable;
  - `injective-binary-automata-have-formalizable-left-inverses`, since some injective automaton has
    no formalizable left inverse.
- **Two routes are invalidated:** `formalizable-pairs-reduce-surjunctivity-to-kaplansky` and
  `formalizable-left-inverses-reduce-surjunctivity-to-kaplansky`. Their target,
  `stable-finiteness-forces-binary-surjunctivity`, is not refuted and stays open.

**Scope.**
- This decides nothing about Gottschalk's conjecture. The witness is bijective, on a residually
  finite group.
- The one-track degree argument does not reach stable formalization with ancilla tracks, or formal
  pairs after regrouping along a finite-index subgroup. On several tracks the top variable can cancel
  between components.

Artifact, Section 2.
