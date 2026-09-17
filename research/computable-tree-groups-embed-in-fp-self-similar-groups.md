---
rg: 2
id: computable-tree-groups-embed-in-fp-self-similar-groups
kind: claim
title: Every finitely generated group with solvable word problem and a computable faithful regular-tree action embeds in a finitely presented self-similar group
distinct_from:
  every-decidable-group-embeds-in-fp-self-similar-group: that is refuted, because decidable groups need not act faithfully on any regular rooted tree; this adds the computable faithful tree action, and that hypothesis is necessary.
  every-fp-rf-group-embeds-in-fp-self-similar-group: that is restricted to finitely presented inputs; this is a self-similar Higman characterization for all finitely generated inputs, and together with every-fp-rf-group-acts-on-a-regular-rooted-tree it implies that claim.
  rf-higman-embedding-for-decidable-groups: that asks for any finitely presented residually finite overgroup; this asks for a self-similar one and assumes a computable action on a regular tree rather than effective residual finiteness.
---

**OPEN.** Let `H` be a finitely generated group with solvable word problem
that has a faithful action on some `T_d` (`d >= 2`) computable on vertices.
Then `H` embeds in a finitely presented self-similar group.

## The hypotheses are necessary (established here)

Let `S <= Aut(T_d)` be a finitely presented self-similar group with finite
generating set `Sigma`, and let `H <= S` be finitely generated. Then:

1. **`H` has solvable word problem.** `S` acts faithfully on a locally finite
   tree, so it is residually finite. By McKinsey's algorithm a finitely
   presented residually finite group has solvable word problem, and finitely
   generated subgroups inherit this.
2. **The action of `H` on `T_d` is computable.**
   - Self-similarity gives, for each `t in Sigma` and `x in X`, a root
     permutation `pi_t(x)` and a word `w_(t,x)` over `Sigma^{+-1}` with
     `t|_x = w_(t,x)`. This is a finite table.
   - Then `t(x v) = pi_t(x) w_(t,x)(v)` and `(ab)(v) = a(b(v))` compute `u(v)`
     for any word `u` and vertex `v`, by recursion on `|v|`.
   - The generators of `H` are words in `Sigma`.

So the claim says that the finitely generated subgroups of finitely presented
self-similar groups are exactly the finitely generated groups with solvable
word problem and a computable faithful regular-tree action. It is a Higman-type
characterization, with finitely presented self-similar groups in place of
finitely presented groups.

## What it would give

- **With [[every-fp-rf-group-acts-on-a-regular-rooted-tree]]:**
  [[every-fp-rf-group-embeds-in-fp-self-similar-group]], through the route
  [[fp-rf-self-similar-embedding-via-computable-tree-actions]].
- **Alone, on the finite-class KMS groups.**
  - These groups are finitely presented and act faithfully on `T_(d(p))`, by
    [[finite-class-kms-groups-act-on-regular-rooted-trees]]. By
    [[fp-tree-groups-have-computable-faithful-tree-actions]] the action is
    computable.
  - So this claim puts each of them in a finitely presented self-similar group.
  - If that family has word problems of unbounded recursive complexity, this
    gives [[fp-self-similar-groups-with-arbitrarily-hard-word-problem]]. That
    hypothesis is not established in the graph.

## Where it can fail

A counterexample is a finitely generated group `H` with solvable word problem
and a computable faithful tree action that lies in no finitely presented
self-similar group. Such an `H` need not be finitely presented, so the
obstruction does not have to refute
[[every-fp-rf-group-embeds-in-fp-self-similar-group]]. This claim can therefore
fail while that one holds.

- **Rauzy-type candidates** (arXiv:2002.02540) are the natural source. Every
  group satisfying the hypotheses is effectively residually finite through its
  computable level quotients.
- **Weaker Rauzy-type invariants** separate finitely generated subgroups of
  finitely presented residually finite groups from arbitrary effectively
  residually finite groups. Any such invariant that the hypotheses do not force
  would refute this claim.

## Attempts

1. **Section words as a tape (2026-09-17, sketch only).**
   - *The mechanism.* Sections of a product `a_1 ... a_m` at a letter `x` are
     the output of a right-to-left sequential transducer whose state is the
     current letter. Over many levels, iterated sweeps can simulate a tag system
     on the section word, so a finitely generated self-similar group can realize
     computable portraits once idle levels give it room to compute.
   - *Where it stalls, first.* The carry of each sweep is the tree letter
     itself. Using it for computation permutes letters at idle levels, and
     different working branches compute the same group element through
     different words.
   - *Where it stalls, second.* Even a finitely generated self-similar hull
     leaves finite presentation, the Higman step, untouched. No existing
     finitely presented self-similar construction (affine hosts, contracting
     groups through Nekrashevych) contains groups with unbounded word problem
     complexity, by (N2) and `kms-groups-avoid-commutative-algebra-affine-hosts`.
