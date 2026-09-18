---
rg: 2
id: rational-stepping-stones-in-nv-need-bs12-or-heisenberg
kind: claim
title: If Aff(Q), SL_2(Q) or GL_n(Q) (n >= 2) embeds in a Brin-Thompson group nV, so does BS(1,2); if U_3(Q) or GL_n(Q) (n >= 3) does, so does H_3(Z)
distinct_from:
  bs12-embeds-in-brin-thompson-2v: that is the open question whether BS(1,2) embeds in some nV; this claim shows every rational stepping stone of gl-n-q-embeds-in-fp-simple-group implies it.
  heisenberg-group-embeds-in-some-brin-thompson-group: that is the open question for H_3(Z); this claim reduces U_3(Q) and GL_n(Q), n >= 3, to it.
  gl-n-q-embeds-in-fp-simple-group: that is the root; this claim says which open nV questions any nV host for it must first answer.
artifacts:
  - research/artifacts/gq-bt-kojima-mechanism.md
---

**ESTABLISHED** through `rational-stepping-stones-in-nv-need-bs12-or-heisenberg-proof`
(lane proof, not independently reviewed).

**Statement.** Fix `n0 >= 2`, and write `nV` for the Brin--Thompson group
on `n0` coordinates.
1. If one of `Aff(Q) = Q ⋊ Q^x`, the Borel group `B_2(Q)`, `SL_2(Q)`, or
   `GL_n(Q)` for some `n >= 2` embeds in `nV`, then `BS(1,2)` embeds in `nV`.
2. If `U_3(Q)` or `GL_n(Q)` for some `n >= 3` embeds in `nV`, then
   `H_3(Z)` embeds in `nV`.
3. If `GL_n(Q)` for some `n >= 3` embeds in `nV`, then `SL_3(Z)` does, so
   `nV` has an infinite subgroup with property (T).

**Why it matters for the root.** Kojima--Sheng put `Q` in `2V`
(`rationals-embed-in-brin-thompson-group-2v`), and `nV` is finitely presented
and simple, so `nV` is not excluded by O1 or O3 of
`gl-n-q-embeds-in-fp-simple-group`. Unlike `VA`, `nV` also contains distorted
cyclic subgroups (`brin-thompson-mv-contains-a-distortion-element`, growth
`O(log^4 N)`). But every stepping stone of the root that is not virtually
abelian passes through the two gates above. Both are OPEN:
`bs12-embeds-in-brin-thompson-2v` (an 18.7-million-table search found no
witness) and `heisenberg-group-embeds-in-some-brin-thompson-group`. For
`n >= 3`, item 3 would also refute `kazhdan-subgroups-of-brin-thompson-groups-are-finite`.
So a plain `nV` host for `GL_n(Q)` must first settle those questions
positively. What `nV` does hold without them is recorded in
`countable-virtually-abelian-groups-embed-in-2v`.
