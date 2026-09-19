---
rg: 2
id: amenable-amalgams-have-mf-full-cstar-citation
kind: route
title: Import Shulman's amenable amalgam theorem
target: amenable-amalgams-have-mf-full-cstar
requires: []
artifacts:
  - notes/FINITE_PACKET_SELF_COPY_COLLAPSE.md
  - notes/FALSE_SHULMAN_TRACE_AUDIT.md
---

Shulman's Theorem 19 states that if `G₁` and `G₂` are amenable, then the full
group C-star algebra of `G₁ *_H G₂` is MF for every common subgroup `H`.
The paper's proof embeds the two full group C-star algebras compatibly into a
UHF algebra and applies its general amalgam criterion.  The theorem is in the
same operator-norm MF convention used by Cairn.

Since every group embeds into the unitary group of its full group C-star
algebra, MF of `C*(G₁ *_H G₂)` implies operator-MF of the group.
