---
rg: 2
id: binary-left-inverse-pairs-need-not-be-formalizable
kind: claim
title: A reversible binary marker automaton over the integers admits no formalizing representatives
invalidates: [formalizable-pairs-reduce-surjunctivity-to-kaplansky]
distinct_from:
  binary-left-inverse-pairs-are-formalizable: that is the universal formalizability claim; this is its negation, witnessed over the integers with alphabet F_2.
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
- By `formalizable-binary-pairs-over-biorderable-groups-are-affine` with `G = Z`, the left-inverse
  pair `(tau, tau)` has no representatives in which `tau o tau = id` holds formally, on any memories.
- So `binary-left-inverse-pairs-are-formalizable` is false, for `G = Z` and `n = 1`.
- The route `formalizable-pairs-reduce-surjunctivity-to-kaplansky` can never complete, and this claim
  invalidates it.
- Its target, `stable-finiteness-forces-binary-surjunctivity`, is not refuted. It stays open, with no
  route through formalizability.

**Scope.** This decides nothing about Gottschalk's conjecture. The witness is bijective, on a
residually finite group.

Artifact, Section 2.
