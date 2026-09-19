---
rg: 2
id: literal-witness-kernel-amenable
kind: claim
title: Amenability of the kernel from the literal group to its Clifford witness
artifacts:
  - non_mf_groups_exist.tex
  - notes/NON_MF_FINAL_REVIEW_AND_RESOLUTION_2026-08-14.md
---

The kernel of the canonical surjection from the literal group `E` to the
Clifford witness `W` is amenable.

**REFUTED by `literal-witness-kernel-free` — this is not a live hole.**  Any
"open but unreachable from any root" warning on this node is expected and
should be read as "refuted", not as "unattempted": the claim is false, and its
only consumer route `literal-sofic-via-amenable-kernel` was invalidated by the
refuter.  Do not re-hang it and do not attempt it.

**Detail (2026-08-14).**  `literal-witness-kernel-free` computes that kernel:
it is a free group of countably infinite rank, so it contains `F_2` and is not
amenable.  See `notes/LITERAL_GROUP_BLOCK_AMALGAM_STRUCTURE_2026-08-14.md`,
Theorem 6.1.  The node is kept only so that the invalidation of
`literal-sofic-via-amenable-kernel` has a named victim; do not attempt it.
