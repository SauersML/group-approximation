---
rg: 2
id: no-type-fn-plus-1-host-via-word-problem-degree
kind: route
title: "If some finite level F_m has no r.e.-complete word problem, a finitely presented group with complete word problem has no F_m host"
target: some-type-fn-group-embeds-in-no-type-fn-plus-1-group
requires:
  - some-type-fm-level-has-no-complete-word-problem
---

Assume `m >= 3` is finite and no group of type `F_m` has an r.e.-complete word
problem.

1. **Hosts dominate word problems.** Let `G = <S | ...>` be finitely generated
   and `φ: G -> H` injective, with `H = <T | ...>` finitely generated. Choose a
   word `w_s` over `T` representing `φ(s)` for each `s` in `S`. A word `v` over
   `S` is trivial in `G` iff `v(w_s)` is trivial in `H`, because `φ` is
   injective. The substitution `v -> v(w_s)` is computable, so the word problem
   of `G` many-one reduces to that of `H`.

2. **A witness candidate.** There is a finitely presented group `B` whose word
   problem is r.e.-complete (Novikov 1955, Boone 1959: the halting set many-one
   reduces to the triviality of special words). The word problem of any
   finitely presented group is r.e.

3. **No host.** Suppose `B <= H` with `H` of type `F_m`. Then `H` is finitely
   presented, so its word problem is r.e. By step 1 the complete word problem
   of `B` reduces to it, so it is r.e.-complete, contradicting the premise. So
   `B` has no host of type `F_m`.

4. **A witness at a level.** Take the least `k` with `3 <= k <= m` such that
   `B` has no host of type `F_k`; step 3 gives `k <= m`. If `k = 3`, then `B` is
   of type `F_2` with no `F_3` host. If `k > 3`, then `B` has a host `K` of type
   `F_{k-1}`, and `K` has no host of type `F_k`, since that would host `B`.
   Either way some group of type `F_n` (`n = k - 1 >= 2`) has no `F_{n+1}` host,
   which is the target claim.

The route is conditional on its premise, which is expected to be false (see
the premise's Attempts). It records exactly what a word-problem degree
obstruction would need. It is unreviewed.
