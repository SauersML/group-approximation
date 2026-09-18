---
rg: 2
id: folner-separators-of-boone-higman
kind: claim
title: A Følner-growth bound U separates Boone--Higman iff every finitely presented simple group has all amenable subgroups below U; below every tower this fails, and uniform witness families cannot show it fails for all recursive U
distinct_from:
  exactness-separates-boone-higman-iff-fp-simple-groups-exact: that separator is exactness, where (S2) is one fixed residually finite group; this is a scale of separators indexed by growth bounds U, where (S2) holds at every recursive U by a diagonal construction and (S1) is killed on the whole elementary range.
  hereditary-approximation-disproofs-of-boone-higman: that treats sofic, MF and hyperlinear separators, with the decidable side open; this treats Følner-growth separators, with the decidable side settled for every recursive bound.
  complexity-bounded-host-classes-are-not-universal: that kills host classes through a shared recursive bound on word-problem complexity; this concerns a bound on the Følner growth of amenable subgroups, and its kill of uniform families goes through Cavaleri's c.e.-class theorem.
  fp-simple-dehn-functions-have-no-recursive-upper-bound: that is about Dehn functions of the finitely presented simple groups themselves; this is about Følner functions of their amenable subgroups.
  boone-higman-conjecture: that is the embedding conjecture; this gives a family of hereditary separators for it, the exact condition for each to work, and the region where none works.
  folner-functions-of-fp-amenable-groups-have-no-recursive-bound: that asks for finitely presented amenable groups beyond every recursive bound; this asks for amenable subgroups of finitely presented simple groups beyond every recursive bound, where the ambient group need not be amenable.
  fp-simple-amenable-subgroups-beat-every-recursive-folner-bound: that is the open statement E that no Følner separator works; this is the separator theorem that reduces the question to E and records the obstructions to proving E.
  decidable-amenable-groups-have-no-recursive-folner-bound: that is the decidable input (D2) used here for (S2).
  iterated-wreath-products-of-z-have-tower-folner-functions: that is the tower bound used here to kill (S1) below towers.
---

**ESTABLISHED** by `folner-separators-of-boone-higman-proof`. The proof is
unreviewed. It combines four prerequisites, each ESTABLISHED in the graph, with
short arguments given in full in the route.

## Setup

Conventions:
- `F_(G,X)(n)` is the least size of a finite `Ω ⊂ G` with `|Ω \ xΩ| <= |Ω|/n`
  for every `x in X`. For finitely generated amenable `G` this is finite.
- `f ≼ U` means `f(n) <= C U(Cn)` for some `C >= 1` and all `n`. The class of
  `F_(G,X)` under `≼` does not depend on the finite generating set `X`, and we
  write `F_G`.
- Separation is in the sense of `hereditary-approximation-disproofs-of-boone-higman`.
  A class `P` closed under isomorphism and subgroups *separates* when
  - (S1) every finitely presented simple group lies in `P`, and
  - (S2) some finitely generated group with solvable word problem does not.

  A separator disproves the Boone--Higman conjecture.

**Definition.** For a non-decreasing `U: N -> N` with `U >= 1`, let `P_U` be the
class of groups `G` such that every finitely generated amenable subgroup `H`
of `G` has `F_H ≼ U`.

## Theorem

Let `U` be non-decreasing with `U >= 1`.

1. **Hereditary and faithful.** `P_U` is closed under isomorphism and subgroups.
   A finitely generated amenable group `G` lies in `P_U` iff `F_G ≼ U`.
2. **Criterion.** `P_U` separates iff (S1_U) and (S2_U), where
   - (S1_U): every finitely presented simple group lies in `P_U`;
   - (S2_U): some finitely generated amenable group with solvable word problem
     has `F ⋠ U`.

   If `U` is recursive then (S2_U) holds. So for recursive `U`, **`P_U`
   separates iff (S1_U)**.
3. **Tower kill.** If `U ≼ exp_k` for some `k`, then (S1_U) fails. The group
   `Z wr (Z wr ... wr Z)` with `k+2` factors embeds in a finitely presented
   simple group and has Følner function `⋠ U`. (Here `exp_0(n) = n` and
   `exp_(j+1)(n) = 2^(exp_j(n))`.)
4. **Uniform-family kill.** Call a computable sequence `e -> (S_e, Y_e)` a
   *certified family* when each `S_e` is a finite presentation, each `Y_e` is a
   finite tuple of words, and every `H_e = <Y_e> ≤ S_e` is amenable. Simplicity
   of `S_e` is not required. For every certified family there is one recursive
   `U_*` with `F_(H_e) ≼ U_*` for all `e`. The same holds for any
   recursively enumerable class of recursive presentations of amenable
   groups, whatever their hosts. So no argument that picks the witnesses for
   all recursive `U` from one such family can refute every (S1_U). The towers
   `W_k` of item 3 form such a class.
5. **Conditional.** The Boone--Higman conjecture implies
   `fp-simple-amenable-subgroups-beat-every-recursive-folner-bound` (E): for
   every recursive `U`, some finitely presented simple group has a finitely
   generated amenable subgroup with `F ⋠ U`. Equivalently, a single recursive
   `U` satisfying (S1_U) disproves the conjecture. By item 3 such a `U`
   satisfies `F_(W_k) ≼ U` for every `k`, so `U ⋠ exp_k` for every `k`.

## Reading

- The decidable side is closed for the whole recursive scale. What remains is
  the single statement E about amenable subgroups of finitely presented simple
  groups, and E is a consequence of the conjecture. So this separator family
  can disprove Boone--Higman only through a recursive `U` above every tower.
- Item 4 names the invariant that stops the natural proofs of E: membership of
  the witnesses in one recursively enumerable class of amenable presentations.
  Any proof of E must choose witnesses whose amenability is not uniformly
  certified. In practice this means the construction uses the totality of `U`,
  as the decidable construction D2 does.
- For recursive `U` that is not monotone, apply the theorem to the running
  maximum `max_(m<=n) U(m)`, which is recursive, non-decreasing and at least `U`.
