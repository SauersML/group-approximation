---
rg: 2
id: linear-and-metabelian-groups-embed-in-isolated-groups
kind: claim
title: Every finitely generated group linear over a finite product of fields, in particular every finitely generated linear or metabelian group, embeds in an isolated group
distinct_from:
  every-decidable-group-embeds-in-an-isolated-group: that is Cornulier--Guyot--Pitsch Question 4 for every finitely generated group with solvable word problem; this answers it for the finitely generated quasi-linear groups, which include all finitely generated linear and metabelian groups.
  quasi-linear-groups-satisfy-permutational-boone-higman: that puts these groups in the permutational Boone--Higman class and hence in finitely presented simple groups; this records the consequence for the printed isolated-embedding question.
---

**ESTABLISHED** by `isolated-overgroups-via-permutational-boone-higman-class`.

**Statement.** Let `G` be a finitely generated group that embeds in
`GL_(n_1)(K_1) x ... x GL_(n_r)(K_r)`, where the `K_i` are fields of arbitrary
characteristics. Then `G` embeds in an isolated group. This covers every
finitely generated linear group over a field, in any characteristic, and every
finitely generated metabelian group.

So Cornulier--Guyot--Pitsch Question 4 (arXiv:math/0511714, TeX lines
828–830) has a positive answer on this class; see
`every-decidable-group-embeds-in-an-isolated-group`.

**What this does and does not add.** Mathematically it is a one-line
consequence of the Boone--Higman results on main. The inputs are
`quasi-linear-groups-satisfy-permutational-boone-higman`, independently reviewed
PASS in `research/artifacts/review-metabelian-bh-2026-09-13.md`, and the
observation that finitely presented simple groups are isolated. It is recorded
because Question 4 is printed separately from Boone--Higman, and these cases of
it follow. No priority is claimed beyond that of the Boone--Higman chain it
consumes, whose characteristic-p and metabelian parts are recent repository
results.
