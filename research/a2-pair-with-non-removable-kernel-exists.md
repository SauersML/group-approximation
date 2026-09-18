---
rg: 2
id: a2-pair-with-non-removable-kernel-exists
kind: claim
title: Some type [A_2] pair sharply embeds in no type [A_2] pair with finitely normally generated kernel
distinct_from:
  a2-pairs-embed-in-a2-pairs-with-fng-kernels: that is the universal assertion of the first part of FFWZ Question 5.9; this is its negation, and that node names this one in refuted_by.
  a2-kernel-removal-forces-recursive-kernel: that proves removable kernels are recursive; this asserts that some pair violates removability.
  a2-kernel-removable-iff-image-in-type-a2-actor: that characterizes removability of one pair by its image; this asserts one pair whose image lies outside that class.
artifacts:
  - research/artifacts/solve-mixed-identity-undecidable-2026-09-13.md
---

**ESTABLISHED** (2026-09-18, lane proofs, not reviewed) through
`non-removable-a2-kernel-from-nonrecursive-kernel`, from `some-a2-action-has-a-nonrecursive-kernel`.
Some group `G` has a type `[A_2]` action on `S`, in the sense of
Fournier-Facio--Wu--Zaremsky (arXiv:2603.24687), with kernel `K`, such that
`(G, K)` sharply embeds in no `(G', K')` with `G' ↷ S'` of type `[A_2]` and `K'`
finitely normally generated in `G'`.

This is the negation of the first part of FFWZ Question 5.9, quoted in
`a2-pairs-embed-in-a2-pairs-with-fng-kernels`. Once it is ESTABLISHED, that claim
becomes REFUTED.

**Known sufficient input.** `non-removable-a2-kernel-from-nonrecursive-mixed-identities`
derives it from `fp-simple-group-with-nonrecursive-mixed-identities`.

**Constraint on a witness.** By Attempt 4 of the Question 5.9 node, a witness
with recursive kernel would refute FFWZ Conjecture 1.5. So under that
conjecture, every witness has a non-recursive kernel.
