---
rg: 2
id: some-type-fn-group-embeds-in-no-type-fn-plus-1-group
kind: claim
title: "Some group of type F_n (n >= 2) embeds in no group of type F_{n+1}, hence in no group of type F_infinity"
distinct_from:
  some-finitely-presented-group-embeds-in-no-f-infinity-group: that forbids only F_infinity hosts and is weaker; this forbids F_{n+1} hosts for some n, which implies it but is not implied by it
  every-type-fn-group-embeds-in-a-type-fn-plus-1-group: that is the affirmative first part of Problem 1.1; this is its negation
---

There are `n >= 2` and a group `G` of type `F_n` such that no group of type
`F_{n+1}` contains a copy of `G`. Every group of type `F_∞` is of type
`F_{n+1}`, so `G` has no host of type `F_∞` either.

This is the negative answer to the first part of Zaremsky Problem 1.1 (root
`zaremsky-1-01-type-fn-groups-embed-in-type-fn-plus-1`). The route
`zaremsky-1-01-by-no` requires it and answers both parts negatively. The route
`no-f-infinity-host-from-no-type-fn-plus-1-host` derives the weaker
`some-finitely-presented-group-embeds-in-no-f-infinity-group` from it. The
converse implication fails in general: a group could have hosts
`K_3 <= K_4 <= ...` with `K_m` of type `F_m` and no host of type `F_∞`.

**One-group form.** Let `U` be a universal finitely presented group (Higman
1961), which contains a copy of every finitely presented group. This claim
holds iff there is `m >= 3` such that `U` embeds in no group of type `F_m`.

- If `G` of type `F_n` has no `F_{n+1}` host, then `G <= U`, so `U` has no
  `F_{n+1}` host; take `m = n + 1`.
- Conversely take the least `m >= 3` with no `F_m` host for `U`. If `m = 3`,
  then `G = U` is of type `F_2` with no `F_3` host. If `m > 3`, then `U` has a
  host `K` of type `F_{m-1}`, and `K` has no `F_m` host, since that would host
  `U`; take `n = m - 1 >= 3` and `G = K`.

So an obstruction argument can work with the single group `U`, and any witness
comes from the least level at which `U` fails. The same form appears as `E_m`
in the root.

## Attempts

- **The classical examples are not witnesses** (established:
  `standard-fn-not-fn-plus-1-groups-embed-in-type-f-groups`). The
  Bieri--Stallings and Bestvina--Brady groups are subgroups of type-`F` groups
  (products of free groups, right-angled Artin groups). Abels' groups are
  subgroups of `GL_n(Z[1/p])`, which is of type `F_∞`. All of them have `F_∞`
  hosts, so a witness must lie outside these families.

- **Cardinality-gap arguments are dead** (established:
  `cardinality-does-not-obstruct-type-f-infinity-embedding`). For `n >= 2` the
  groups of type `F_n` and of type `F_{n+1}` both form countable classes. The
  device that separates `FP` from finite presentability, Leary's `2^{ℵ_0}`
  groups of type `FP`, has no analogue. Diagonal arguments over the countable
  list of finite presentations are not excluded by this. By the one-group form
  above they reduce to showing that `U` itself avoids every group of type `F_m`
  for some `m`. No invariant separating `U` from all subgroups of `F_m` groups
  is known.

- **Unsolvable word problem alone is not an obstruction** (established:
  `unsolvable-word-problem-does-not-obstruct-type-f-infinity`). There is a
  group of type `F` with unsolvable word problem. It hosts itself, so
  unsolvability does not rule out an `F_∞` host.

- **Word-problem degree: an open reduction** (route
  `no-type-fn-plus-1-host-via-word-problem-degree`, premise
  `some-type-fm-level-has-no-complete-word-problem`). If `H` hosts `G`, the word
  problem of `G` many-one reduces to that of `H`. `U` has an r.e.-complete word
  problem. So if some finite level `F_m` (`m >= 3`) contains no group with
  r.e.-complete word problem, `U` has no `F_m` host and this claim follows. The
  premise is expected to be false (see its Attempts). A type-`F` group with
  r.e.-complete word problem would kill the route.

- **The natural universal construction is blocked at level 3** (established:
  `higman-rope-trick-group-is-never-fp3`; dead route
  `type-fn-hosts-via-higman-rope-trick`). The Higman rope-trick container
  `Hig_ι(G)` is never of type `FP_3(Q)` for infinite `G = F/R` with `R != 1`
  (Fournier-Facio--Zaremsky, arXiv:2607.21727v1, Theorem B). This kills a
  method for the affirmative answer, not every host, so it is no witness. The
  same paper's Theorem A (`ffz-rp-fpn-embedding-gives-fp-fn-embedding`)
  is a lever for the affirmative side.

- **What a genuine obstruction needs.** It needs an invariant that `U` has and
  that no subgroup of a type-`F_m` group has, for some finite `m >= 3`.
  Cohomological dimension is not one: hosts may have larger dimension. For
  `L^2`-Betti numbers and Novikov--Shubin invariants this lane knows no
  statement that bounds a subgroup's invariants by the finiteness type of a
  host; that is a bounded check, not a literature survey. No candidate is known.
  Fournier-Facio--Zaremsky (arXiv:2607.21727v1, Introduction) record Problem 1.1
  as open.
