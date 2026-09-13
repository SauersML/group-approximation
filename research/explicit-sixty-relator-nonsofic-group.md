---
rg: 2
id: explicit-sixty-relator-nonsofic-group
kind: claim
title: An explicit presentation with seven generators and sixty relators defines a finitely presented simple nonsofic group
distinct_from:
  fp-simple-nonsofic-group: that is existence of a finitely presented simple nonsofic group, witnessed through Khanh's Theorem 6.1 whose presentation is not usable; this names one presentation, sixty relators of total length 1007, whose group is simple and nonsofic.
  finitely-presented-nonsofic-group-exists: that is the kernel-checked existence of a finitely presented nonsofic group through a finite-table cover whose relators are never written; this writes the relators.
  sofic-quotient-nonclosure: that is existence of a fixed two-generator finitely presented nonsofic quotient of F_2 whose relators are not written; this is an explicit seven-generator list.
---

**ESTABLISHED (2026-09-12, unreviewed)** through
`explicit-sixty-relator-nonsofic-group-proof`.

The group

```text
P = < c, t, y_1, y_e, y_f, y_E, y_F |
      t^2, c^5, (tc)^4, (tc^-1tc)^3, (tc^-2tc^2)^2,
      [y_a, c^2tc^-2], [y_a, c^-2tc^2],  (t y_1)^3,  y_1^2,
      17 commutation relators,  13 + 12 Steinberg product relators,  1 partition relator >
```

of `leavitt-unit-group-steinberg-weyl-presentation` is finitely presented, simple and not
sofic. Its sixty relators have total length 1,007, and the longest has length 38.

It is also integrally acyclic, being `L_(F_2)(1,2)^x` (`leavitt-steinberg-map-iso-from-rank-three`,
(KH1)).

## Why this object

Before 2026-08-01 no nonsofic group was known. After that date, the finitely presented
nonsofic groups on record were a finite-table cover with no relators written; Khanh's
presentation, with `20(4^195-1)/3` generators; and a 4,648-entry atlas list, which presents
only a central extension relative to the atlas. `P` is the first nonsofic group whose
defining relations fit on half a page. It invites the extremal questions it does not settle:
- the least number of relators, and the least total relator length, of a nonsofic group;
- whether a nonsofic group can have a presentation of deficiency zero with short relators.
