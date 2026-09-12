---
rg: 2
id: fp-self-similar-subgroups-satisfy-permutational-boone-higman
kind: claim
title: Subgroups of finitely presented self-similar groups, and finitely generated linear groups over number fields, lie in the permutational Boone--Higman class
distinct_from:
  fp-self-similar-groups-embed-in-fp-simple-groups: that is Zaremsky's embedding of a finitely presented self-similar group in a finitely presented simple group; this upgrades the conclusion to membership in B_A, the class that is closed under direct products and finite extensions.
  algebraic-linear-groups-satisfy-boone-higman: that is Boone--Higman for finitely generated linear groups over number fields; this puts the same groups in B_A.
  boone-higman-type-a-class-closed-under-finite-extensions: that is permanence of B_A; this supplies two new families of members of B_A.
artifacts:
  - research/artifacts/bh-metabelian-products-2026-09-12.md
---

**ESTABLISHED.** Let `B_A` be the class of groups that embed in a group admitting
an action of type (A), as in
`boone-higman-type-a-class-closed-under-finite-extensions`. By
Belk--Fournier-Facio--Hyde--Zaremsky arXiv:2503.21882v2, these are the groups
satisfying the permutational Boone--Higman property.

(a) Every subgroup of a finitely presented self-similar group lies in `B_A`.

(b) Every finitely generated subgroup of `GL_n(K)`, for `K` algebraic over `Q`,
lies in a finitely presented self-similar group, and hence in `B_A`.

Consequently every finite direct product of such groups, and each of their
finite-index overgroups, has solvable word problem and embeds in a finitely
presented simple group.

**Credit: known in substance.** BFFHZ arXiv:2503.21882v2 give both ingredients:
- *Remark 3.5:* all finitely presented commutator subgroups of
  Röver--Nekrashevych groups are highly transitive.
- *Theorem C:* every finitely presented simple highly transitive group, "as does
  every subgroup thereof", satisfies the permutational conjecture.

Zaremsky's envelope for a finitely presented self-similar group is such a
commutator subgroup, so (a) is an immediate combination. Part (b) reads the
finitely presented self-similar group off Zaremsky's proof of his Theorem 1.2.
The node is recorded because the graph consumes it; no priority is claimed.

Inputs, as Cairn nodes:
- `fp-self-similar-groups-embed-in-fp-simple-groups` (Zaremsky's envelope);
- `rover-nekrashevych-groups-are-highly-transitive`;
- `fp-simple-highly-transitive-groups-satisfy-pbh` (BFFHZ Theorem C).

The derivation is `fp-self-similar-subgroups-satisfy-pbh-proof`.
