---
rg: 2
id: leavitt-square-unit-groups-mod-scalars-satisfy-pbh
kind: claim
title: For every prime p the finitely presented simple group (L_(F_p)(1,2) ⊗ L_(F_p)(1,2))^× / F_p^× admits an action of type (A), so it and all its subgroups satisfy permutational Boone--Higman
distinct_from:
  leavitt-unit-groups-mod-scalars-satisfy-pbh: that is the one-factor group L_(F_p)(1,2)^× / F_p^×; this is the tensor square, which admits no unital algebra map into the one-factor algebra over F_2.
  positive-char-surface-linear-groups-satisfy-boone-higman: that places surface-linear groups inside this group and draws plain Boone--Higman; this gives the group itself, and so every subgroup, the permutational property.
  char-p-linear-groups-satisfy-permutational-boone-higman: that covers finitely generated linear groups in positive characteristic through self-similar hosts; this is the host group itself, which contains Thompson's group V and is not claimed to be linear.
  fp-simple-groups-embed-in-fp-simple-mif-groups: that is BFFHZ Question 3.4 for all finitely presented simple groups; this answers it for these groups.
---

**ESTABLISHED** through `leavitt-square-units-pbh-via-chen-line-action` (not
independently reviewed; no novelty is claimed).

Let `p` be a prime, `L_p = L_(F_p)(1,2)`, and `G^(2)_p = (L_p ⊗ L_p)^× / F_p^×`. Then:
- `G^(2)_p` acts on the lines of the tensor-square Chen module `F_p[D × D]`, and this
  action is of type (A);
- so `G^(2)_p`, and every subgroup of `G^(2)_p`, embeds in a group admitting an action of
  type (A).

**Consequences.**
- **BFFHZ Theorem C.** `G^(2)_p` embeds in a finitely presented simple MIF group
  (`fp-simple-highly-transitive-groups-satisfy-pbh`). So BFFHZ Question 3.4 has a
  positive answer for these finitely presented simple groups.
- **What was open.** The census `research/artifacts/q34-known-actors-coverage-2026-09-13.md`
  listed exactly these groups as not decided, because their germ ideal
  `(s_1 − 1, s_2 − 1)` is not principal.
- **Trust surface.** The finite presentation and simplicity of `G^(2)_p` are imported
  through `odd-leavitt-unit-groups-mod-scalars-are-fp-simple`, which rests on Khanh
  arXiv:2609.08428v1 and Ara--Cortiñas arXiv:1108.0352v3.
