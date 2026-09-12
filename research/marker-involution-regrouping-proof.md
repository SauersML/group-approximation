---
rg: 2
id: marker-involution-regrouping-proof
kind: route
title: Split the flips by residue mod 4 into four track shears and reverse the word
target: marker-involution-is-formalizable-after-regrouping
requires:
  - structurally-reversible-automata-are-formalizable
  - binary-left-inverse-pairs-need-not-be-formalizable
artifacts:
  - research/artifacts/formal-polynomial-strict-pairs-2026-09-12.md
---

Artifact, Section 6.5.
1. The marker at `i` reads offsets `±1, ±2, ±3`, none of them divisible by 4. So `S_r`, which flips
   the cells `4k+r` at markers, reads only the other three tracks of the `4Z`-regrouped
   configuration. It is a track shear.
2. If markers match at `i` and at `j` with `1 <= |i - j| <= 3`, one of the fixed pattern entries
   disagrees. So flipping any subset of the marker set preserves every marker, and the word
   `S_3 S_2 S_1 S_0` flips exactly the markers of the input, which is `tau`.
3. By the first prerequisite the word and its reverse form a formal pair over `4Z`.
4. The second prerequisite is the non-formalizability over `Z` itself, which is the contrast recorded
   in the claim.
