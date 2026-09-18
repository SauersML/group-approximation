---
rg: 2
id: char-zero-upper-triangular-cloning-groups-do-not-embed-in-v
kind: claim
title: "If R has characteristic 0, the Witzel–Zaremsky group T(B_*(R)) does not embed in Thompson's group V"
distinct_from:
  some-finite-cloning-system-group-does-not-embed-in-v: that one uses finite groups and a period-growth obstruction; this one uses infinite matrix groups B_n(R) with char R = 0 and the obstruction is Corwin's Z ≀ Z^2
  cloning-system-groups-on-finite-groups-embed-in-v: that is about finite G_n; B_n(R) is infinite when char R = 0, so this claim neither proves nor refutes it
---

**ESTABLISHED (unreviewed).** Route `char-zero-upper-triangular-cloning-not-in-v-via-corwin`.

**Claim.** Let `R` be a ring with `1 ≠ 0` in which the map `Z → R` is injective. Then the
Thompson-like group `T(B_*(R))` of the Witzel–Zaremsky upper-triangular cloning system
(arXiv:1405.5491, §7) is not isomorphic to any subgroup of Thompson's group `V`.

Examples: `R = Z`, `Q`, `Z[1/p]`, rings of `S`-integers.

This gives a non-local cloning system on linear groups whose Thompson-like group does not embed
in `V`. The obstruction is a subgroup copy of `Z ≀ Z^2`, not torsion growth.
