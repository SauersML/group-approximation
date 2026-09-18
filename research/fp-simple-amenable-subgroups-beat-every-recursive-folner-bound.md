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

     Sub-question (b) is answered negatively for Higman--Thompson hosts in
     Attempt 4.
4. **Short finite expanders: a reduction, and a kill for Higman--Thompson
   hosts (swarm-0917-w10-w10-bh-follow).**
   - **Mechanism.** `short-expander-subgroups-force-folner-growth` (ESTABLISHED)
     splits a Følner set along right cosets of a finite subgroup `Γ ≤ H` and
     averages the Cheeger inequality. If `Γ` has Cheeger constant `>= δ` on
     `<= L` generators of length `<= L`, then `F_H(⌈2L^2/δ⌉) > |Γ|/2`. This is
     the mechanism behind `Δ_U`: its finite lamp subgroups `Q_t` have
     generators of length `<= 2k_t + 1` and order `> t U(t^2 k_t)`.
   - **New decomposition.** The route `fp-simple-folner-growth-via-short-expanders`
     reduces E to the OPEN prerequisite
     `fp-simple-amenable-subgroups-have-unbounded-expander-profile` (E_X). E_X
     can fail while E holds, because the towers are torsion-free.
   - **Kill (named invariant).** The invariant is the finite-subgroup profile
     `FS(L)`: the largest order of a finite subgroup generated by elements of
     length `<= L`. It is monotone under embeddings, and `FS_(Δ_U) ⋠ U`.
     `higman-thompson-finite-subgroup-profile-is-recursive` (ESTABLISHED)
     redoes the pushdown pumping of `almost-automorphism-torsion-subgroups-are-rf`
     with explicit constants. It gives `FS_K ≼ R♯` for one recursive `R♯` and
     every finitely generated `K` in every `V_d` and in every torsion-free
     Röver--Nekrashevych group `V_d(G)`.
     - Failing step: embedding `Δ_U` in `V` (sub-question (b)) is impossible for
       every recursive `U >= R♯`. The same holds for any witness whose Følner
       growth comes from short finite subgroups.
   - **What is left.**
     - A single finitely presented simple host for all `U` must have `FS` above
       every recursive function. With solvable word problem, a recursive bound
       would make its order problem decidable.
     - `2V` is the natural candidate. The pumping fails there, and its torsion
       problem is recalled, not verified at source, to be undecidable
       (Belk--Bleak).
     - The missing step is finite subgroups of `2V` with a uniform Cheeger
       constant on short generators, inside one amenable finitely generated
       subgroup.
     - Sub-question (a), closure of `B_A` under diagonal products, is
       untouched.
4. **The short-expander route, split into two gates (2026-09-18, lane
   `swarm-0917-w11-w11-bh-follow`).** *No construction; one class killed, one gate
   located.*
   - *Mechanism.* Coset averaging gives
     `F_H(⌈2L^2/δ⌉) > X^δ_H(L)/2`. The w10 lane found this, and it is re-proved
     in `amenable-recursive-groups-have-recursive-expander-profile`. So short
     finite expanders inside `H` force Følner growth.
   - *Single subgroup: killed.* By Cavaleri's Theorem 3.1, each finitely
     generated amenable subgroup of a finitely presented group has recursive
     `X^δ`. That is item 2 of the node above. The invariant is Cavaleri's
     recursive Følner bound. The failing step is asking one `H` to serve every
     `U`.
   - *Single host, varying subgroups: split.* The route splits into
     G1 (host expansion) and G2 (amenable localization), recorded on
     `fp-simple-short-expander-profiles-escape-recursive-bounds`.
   - *Where G1 stands.*
     - Its necessary finiteness condition is exactly decidability. That is
       `finiteness-decidable-iff-finite-subgroup-profile-recursive`.
     - The condition fails in the Higman--Thompson groups (w10) and holds in
       `2V`, by `brin-thompson-torsion-orders-escape-every-recursive-bound`.
     - Torsion alone does not give expanders, by
       `abelian-finite-expanders-have-recursively-bounded-order`.
     - One functorial step does, in `EL_3(F_2[2V])`, by
       `torsion-amplifies-to-kazhdan-expanders-over-group-rings`. That
       group has solvable word problem but is not known to embed in a finitely
       presented simple group.
   - *Where it dies now.* Those expanders sit in a Kazhdan group. Nothing here
     moves them into amenable subgroups that vary with `U` and escape the
     certified-family kill of Attempt 2. That is G2, and it is the open step.
