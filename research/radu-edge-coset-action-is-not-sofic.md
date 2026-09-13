---
rg: 2
id: radu-edge-coset-action-is-not-sofic
kind: claim
title: The action of Radu's arithmetic quotient on the oriented x/z-edges of the Cayley graph of PGL_2(Z) is not a sofic set action
distinct_from:
  radu-edge-coset-action-is-sofic: this is its negation
  coordinate-action-not-sofic: that is nonsoficity of the Kun-Thom coset action through property (T) of the stabilizer; this would be a nonsofic set action of a Haagerup lattice with a-T-menable stabilizer
  radu-metabelian-quotient-is-not-sofic: that is nonsoficity of the group G_2; this is nonsoficity of the set action hosting it, which does not imply that claim
---

**OPEN.** `Q ↷ Q/C_χ`, with `C_χ = <a, b, cac, cbc>`, is not sofic in the sense of
Gao–Kunnawalkam Elayavalli–Patchell, Definition 2.1(5).

**Consequences.**
* The only known positive route for `k = 2`, `radu-metabelian-quotient-sofic-via-edge-coset-action`,
  would never fire.
* It would give a nonsofic set action of a sofic, residually finite, Haagerup lattice whose
  stabilizer is a free product of four involutions. The one known nonsofic coset action,
  `coordinate-action-not-sofic`, needs property (T) of the stabilizer.
* It does not imply `radu-metabelian-quotient-is-not-sofic`: Theorem 3.6 of Gao–Kunnawalkam
  Elayavalli–Patchell goes one way only.

**Conditional proof.** `radu-edge-coset-action-not-sofic-via-stability` derives it from flexible
permutation stability of `Q` and a uniform Cheeger constant for `C_χ` on finite `Q`-sets, together with
the established square firewall `radu-square-lamp-forces-reflections-in-finite-actions`.
