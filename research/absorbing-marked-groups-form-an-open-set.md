---
rg: 2
id: absorbing-marked-groups-form-an-open-set
kind: claim
title: Absorbing at a fixed alphabet size is an open condition on marked groups, so a group that absorbs yields a finitely presented group that absorbs
distinct_from:
  absorptions-give-post-surjective-strict-pairs: that proves co-induction up from subgroups and restriction down to a finitely generated subgroup; this proves openness in the space of marked groups, which passes further down to finitely presented groups.
  no-group-carries-a-topological-bernoulli-absorption: that is the open universal statement; this proves it needs checking only on finitely presented groups.
---

**ESTABLISHED (elementary)** by [[absorbing-marked-groups-form-an-open-set-proof]].

**Statement.** Fix `d >= 2`.
- For a finitely generated group `G` with a finite generating tuple `s`, the property "`G` absorbs at size `d`"
  depends only on the labelled ball of some finite radius `r` in the Cayley graph of `(G, s)`. The radius depends on
  the absorption.
- So the set of marked groups that absorb at size `d` is open in the space of marked groups.

**Consequences.**
1. If some group absorbs at size `d`, then some finitely presented group absorbs at size `d`. So
   `no-group-carries-a-topological-bernoulli-absorption` holds for all groups if and only if it holds for all
   finitely presented groups.
2. An absorbing marked group is not a limit of non-absorbing marked groups. In particular it is not a limit of
   sofic groups, which matches the fact that the sofic groups form a closed set of marked groups.

**Note on openness of non-surjunctivity.** The analogous openness of non-surjunctivity is standard: surjunctive
marked groups form a closed set. What is new is that the whole absorption, not only a strict pair, has a
finite-ball witness.
