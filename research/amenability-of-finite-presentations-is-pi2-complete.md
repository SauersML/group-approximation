---
rg: 2
id: amenability-of-finite-presentations-is-pi2-complete
kind: claim
root: true
title: Amenability of finitely presented groups is Pi-zero-two complete
distinct_from:
  amenability-of-finite-presentations-arithmetical-position: that is the unconditional strict-interval placement; this is the completeness statement, which needs a Pi-zero-two hard family of finite presentations with amenable positive branch.
  sofic-recognition-finite-presentations-is-pi2-complete: that needs a sofic-safe compiler and Higman-type embeddings are at least conceivable there; here every Higman-type ambient contains free subgroups, so a compiler in that sense cannot exist and a different mechanism is required.
---

OPEN.  `AMENABLE_fp` is `Pi^0_2`-complete, i.e. there is a computable map
from `INF` (or `TOT`) to finite presentations whose group is amenable on
the positive side and non-amenable on the negative side.

## Why the standard route is closed

Every known compiler from recursive to finite presentations embeds the
recursive group in an HNN tower over free subgroups; such towers contain
`F_2` on both branches, so the positive branch can never be amenable.
Amenability has no Higman embedding theorem and cannot have one in the
naive sense: a finitely presented amenable group containing a prescribed
recursively presented amenable group would have to avoid every free
subgroup while encoding an enumeration.

## What a proof would need

A directly finitely presented family, presumably inside a class of
finitely presented amenable groups with undecidable word problem
([[finitely-presented-amenable-undecidable-word-problem]]), in which a
`Pi^0_2` event (every stage eventually confirmed) keeps the group amenable
while its failure makes a free subgroup appear.  The two-generator
recursive family [[shift-raag-family-classifies-amenability]] shows the
shape of the switch; its finite-presentation analogue would need the
relators `[a, t^j a t^-j]` for all `j` to be consequences of finitely many,
which is exactly what fails.
