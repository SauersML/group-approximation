---
rg: 2
id: some-fp-simple-group-has-an-infinite-bounded-exponent-subgroup
kind: claim
title: Some finitely presented simple group contains an infinite finitely generated subgroup of bounded exponent
distinct_from:
  free-burnside-groups-satisfy-boone-higman: that asks for an embedding of the free Burnside group B(m,n) itself (BBMZ Problem 5.3(6)); this asks only for SOME infinite f.g. bounded-exponent subgroup of SOME finitely presented simple group, which is strictly weaker and is exactly what a bounded-exponent separator of Boone--Higman would deny.
  fp-simple-groups-with-arbitrarily-complex-word-problem: that is the complexity consequence of Boone--Higman, the only surviving decision-problem separator; this is a consequence of a different kind, a hereditary group-theoretic property that is not a decision problem.
  bh-separators-must-omit-nested-decidable-hosts: that classifies decision-problem separators and proves host transfer for every separator; this names one separator outside its tables and the single open statement it turns on.
  circle-and-tree-product-periodic-subgroups-are-finite: that is an established lemma excluding circle groups and tree-product lattices as witnesses; this is the open existence statement.
requires:
  - circle-and-tree-product-periodic-subgroups-are-finite
  - brin-thompson-2v-is-torsion-locally-finite
  - bh-separators-must-omit-nested-decidable-hosts
  - hereditary-approximation-disproofs-of-boone-higman
artifacts:
  - research/artifacts/gq-bh-bh-free-06-one-stack-pumping.md
---

**OPEN.** There are an integer `n >= 1` and a finitely presented simple group `S`
containing an infinite finitely generated subgroup `B` with `b^n = 1` for all
`b ∈ B`.

## Why it matters: a bounded-exponent separator

For `n >= 1` let `P_n` be the class of groups all of whose finitely generated
subgroups of exponent dividing `n` are finite. It is closed under isomorphism and
subgroups. In the language of `hereditary-approximation-disproofs-of-boone-higman`,
`P_n` **separates** Boone--Higman iff
- (S1) every finitely presented simple group lies in `P_n`, and
- (S2) some finitely generated group with solvable word problem does not.

(S2) holds for every odd `n >= 665`: the free Burnside group `B(2,n)` is infinite
and has solvable word problem (Novikov--Adian; Adian's monograph *The Burnside
problem and identities in groups*, 1979; classical, not re-read here). So:

> **For odd `n >= 665`, `P_n` separates Boone--Higman iff this claim fails for
> that `n`.** A proof that no finitely presented simple group contains an infinite
> f.g. group of exponent `n` would therefore disprove `boone-higman-conjecture`.
> Conversely, Boone--Higman (indeed `free-burnside-groups-satisfy-boone-higman`)
> implies this claim.

This separator is not a decision problem, so it lies outside the tables of
`bh-separators-must-omit-nested-decidable-hosts` §2–3, which show that every
hereditary decision-problem separator other than word-problem complexity dies.
It is consistent with that node's host-transfer theorem (§1):
- Clapham's embedding gives a finitely presented group with solvable word problem
  containing `B(2,n)`. Olshanskii--Sapir's finitely presented
  torsion-by-cyclic groups (*Non-amenable finitely presented torsion-by-cyclic
  groups*, Publ. Math. IHES 96, 2002; not re-read) are explicit finitely presented
  groups with infinite bounded-exponent subgroups.
- So finite presentability alone never forces `P_n`, and any proof of (S1) must
  use simplicity together with finite presentation, exactly as that node requires
  of every separator.

## Which finitely presented simple groups cannot be witnesses

A witness `S` must contain an infinite f.g. periodic group of bounded exponent.
- By `circle-and-tree-product-periodic-subgroups-are-finite`, `S`
  acts faithfully on no circle and acts properly on no finite product of trees.
  So `T`, `T_{n,r}`, piecewise-projective circle groups, Burger--Mozes/Wise lattices
  and rank-2 Kac--Moody lattices are all excluded.
- Every subgroup of `S` of the form below is excluded as the home of `B`, by the
  reasons recorded in `free-burnside-groups-satisfy-boone-higman`: residually
  finite (Zelmanov), hence linear or self-similar; hyperbolic; acting properly on a
  finite-dimensional CAT(0) cube complex. So `B` must meet the non-residually-finite,
  non-tree part of the host.

**Not excluded, and the sharpest open cases.** The Cantor-set families:
- Thompson's `V` and Brin--Thompson `nV`;
- Röver--Nekrashevych groups `V_d(G)`, which can contain infinite f.g. periodic
  groups (Röver's group contains Grigorchuk's group, of unbounded exponent);
- twisted Brin--Thompson groups `SV_G` and finite germ extensions of `V`;
- lattices in products of higher-dimensional buildings.

The most concrete test is: **does `V` (or `2V`) contain an infinite finitely
generated subgroup of bounded exponent?** A yes proves this claim. A no, for all
Cantor-set families built from finite-state or germ data, would show that every
host construction on main misses bounded-exponent inputs, and would leave (S1) as
the first non-decision-problem candidate for a counterexample to Boone--Higman.

## Attempts

1. **Where a witness must live (2026-09-18, lane `bh-free-06`).** *Constraints
   only, no witness and no proof of (S1).* The separator reading and the host
   exclusions above. No argument that `V` has only finite f.g. bounded-exponent
   subgroups was found.
   - The tree fixed-point argument fails for `V`: the natural `V`-complexes are
     infinite-dimensional.
   - The rotation-number argument has no analogue on the Cantor set.
2. **Thompson's `V` is not a witness; the sharpest open host is `2V` (2026-09-18,
   lane `bh-free-06`).** `V` is torsion locally finite (Röver; Burillo--Cleary--Röver,
   arXiv:1402.3860, Theorem 1.3). The one-stack pumping re-proof in
   `research/artifacts/gq-bh-bh-free-06-one-stack-pumping.md` also covers `V_{n,r}`,
   and it shows that the argument breaks exactly at a second stack. So `V`, `F`, `T`
   and `V_{n,r}` are excluded as witnesses.
   - The open two-stack case is `brin-thompson-2v-is-torsion-locally-finite`.
   - The full-shift topological full group `[[σ]]` sits inside `2V`, which gives
     concrete candidates there.
   - The withdrawn arXiv:2209.11982 was the only published claim about torsion in
     `nV`.
3. **The read-only head subgroup of `2V` is excluded (2026-09-18, lane
   `bh-free-06`).** `full-shift-topological-full-groups-are-torsion-locally-finite`
   shows that `[[Σ^Z]] ≤ 2V` has no infinite finitely generated torsion subgroup of
   any exponent. For bounded exponent this also follows from residual finiteness of
   `[[Σ^Z]]` together with Zelmanov. A witness inside `2V` must use writing
   machines, for example `RTM(Z,2,1)`. `RTM(Z,2,1)` is LEF (arXiv:1603.08715,
   Theorem 6), and Zelmanov does not apply directly to LEF groups.
