---
rg: 2
id: binary-nonformalizable-pair-over-integers-proof
kind: route
title: The six-cell marker involution is not an affine translation, and formalizable one-track pairs over Z are
target: binary-left-inverse-pairs-need-not-be-formalizable
requires:
  - formalizable-binary-pairs-over-biorderable-groups-are-affine
artifacts:
  - research/artifacts/binary-formalizability-refutation-2026-09-12.md
---

Section 2 of the artifact, in three steps.

1. **Lemma 2.1:** a marker at `i` needs `x_(i±1) = 1`. A marker at any `j` with
   `1 <= |j − i| <= 3` needs `0` at `i − 1` or `i + 1`. So markers within distance 3 exclude each
   other.
2. **Proposition 2.2:** the flipped cells are never read by other markers. The cells a nearby marker
   would need changed are `i ± 1`, which don't flip. So the flip set is invariant, and `tau` is an
   involution.
3. **Proposition 2.3:** `tau` fixes a configuration with a single `1`, and it changes the
   configuration that is `1` exactly at `−1` and `+1`. So it is not affine.

`Z` is bi-orderable, so the prerequisite applies.
