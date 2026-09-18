---
rg: 2
id: fp-simple-amenable-subgroups-beat-every-recursive-folner-bound
kind: claim
title: For every recursive U some finitely presented simple group has a finitely generated amenable subgroup whose Følner function is not bounded by U
distinct_from:
  folner-functions-of-fp-amenable-groups-have-no-recursive-bound: that needs the amenable group itself finitely presented, Gromov's question; this lets it be any finitely generated subgroup of a finitely presented simple group, which is itself non-amenable.
  fp-simple-dehn-functions-have-no-recursive-upper-bound: that concerns Dehn functions of the simple groups; this concerns Følner functions of their amenable subgroups, and neither implies the other by any known argument.
  decidable-amenable-groups-have-no-recursive-folner-bound: that is the decidable version, established with no simple host; this asks for a finitely presented simple host.
  folner-separators-of-boone-higman: that is the separator theorem, which shows the conjecture implies this statement and kills two proof classes; this is the remaining open statement.
---

**OPEN.** Call this statement E. For every recursive non-decreasing
`U: N -> N` there are a finitely presented simple group `S` and a finitely
generated amenable `H ≤ S` with `F_H ⋠ U`. Here `F_H` is the Følner function
and `≼` is the order `f(n) <= C U(Cn)`, as in `folner-separators-of-boone-higman`.

By `folner-separators-of-boone-higman`, E fails iff some recursive `U` makes
`P_U` a separator. So a refutation of E disproves Boone--Higman.

One route leads here: `fp-simple-amenable-folner-growth-via-boone-higman`,
which is conditional on `boone-higman-conjecture`.

## Attempts

1. **Iterated wreath towers (done for the elementary range; stops there).**
   `W_(k+2) = Z wr (... wr Z)` embeds in a finitely presented simple group and
   has Følner function `⋠ exp_k`. So E holds for every `U ≼ exp_k`, and in
   particular for every Kalmár-elementary `U`. The tower family cannot reach
   all recursive `U`. It is a recursively enumerable class of amenable
   presentations, so Cavaleri's Corollary 3.6 bounds all of it by one recursive
   function (item 4 of `folner-separators-of-boone-higman`).
2. **Any certified uniform family (killed).** Suppose the witnesses are drawn
   from a computable sequence of finite presentations `S_e`, with finite tuples
   `Y_e` such that every `<Y_e>` is amenable. This covers every family produced
   effectively from fixed amenable seeds by amenability-preserving operations,
   such as restricted wreath products, finite extensions and direct products,
   whatever simple hosts are then used.
   The subgroup presentations form a recursively enumerable class of amenable
   presentations. Cavaleri's Corollary 3.6 gives one recursive `U_*` bounding
   them all, and the approach dies at `U = U_*`.
   - Invariant: membership of the witnesses in one c.e. class of amenable
     presentations.
   - Consequence: a proof of E must use the totality of `U` in building the
     witness, as the decidable construction does.
3. **Embed the Brieussel--Zheng diagonal products (live; missing one step).**
   The groups `Δ_U` of `decidable-amenable-groups-have-no-recursive-folner-bound`
   use the totality of `U`, so they escape the obstruction of Attempt 2. Under
   Boone--Higman they embed, which is the conditional route. Unconditionally,
   the missing step is an embedding of each `Δ_U` in a finitely presented
   simple group. What is known about `Δ_U`:
   - It is a split extension `M ⋊ Z`, with `M` the normal closure of the lamp
     generators.
   - `M` is locally finite. Finitely many lamp conjugates generate, at every
     level `s` with `k_s` beyond their spread, a copy of the level-0 subgroup,
     so the subgroup they generate is finite.
   - `Δ_U` is residually finite, since it is a subgroup of `Π_s Γ_(s) wr Z`.
   - The obstruction to the naive `B_A` closure argument: each factor
     `Γ_(s) wr Z` lies in `B_A` (finite lamp group), but `Δ_U` lies in no
     finite product of them. The Kaloujnine--Krasner envelope `M wr Z` of
     `M ⋊ Z` is the *unrestricted* wreath product, because the lamp generators
     have nonzero coordinates at every level. So the closure of `B_A` under
     restricted wreath products does not reach `Δ_U`.
   - Two sub-questions, each of which would suffice:
     - (a) Is `B_A` closed under diagonal products of `Γ_(s) wr Z` along a
       recursive sequence of finite factors?
     - (b) Does every `Δ_U` embed in one fixed Thompson-like finitely presented
       simple group, for example `V` or a Röver--Nekrashevych group, through an
       action on a Cantor set that uses deeper cones for larger `s`?

     Neither was tested.
