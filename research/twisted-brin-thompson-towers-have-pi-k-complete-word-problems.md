---
rg: 2
id: twisted-brin-thompson-towers-have-pi-k-complete-word-problems
kind: claim
title: The k-th clopen tower of twisted Brin-Thompson groups over the trivial actor is finitely presented, simple, and has a Pi_k^p-complete word problem
distinct_from:
  twisted-brin-thompson-wp-equals-actor-orbit-problem: that transfers complexity between an actor and SV_G with an upper bound for iterated towers only; this proves the matching lower bound, one full quantifier alternation per level, for one explicit tower.
  fp-simple-group-with-pspace-complete-word-problem: that asks for one finitely presented simple group at the PSPACE rung; this realizes every rung Pi_k^p of the polynomial hierarchy, and no single member is PSPACE-complete unless PH collapses.
  leavitt-square-units-have-conp-parity-p-complete-word-problem: that pins one group at coNP^parityP, with finite presentation and simplicity conditional; this is an unconditional family at Pi_k^p for every k, with a different mechanism (nested stabilizer tests rather than superposed evaluation).
  bh-separators-must-omit-nested-decidable-hosts: that records nV (coNP-complete) as the hardest finitely presented simple group whose complexity the lane determined; this supersedes that bounded-search remark.
  kourovka-7-19-explicit-fp-simple-group-with-non-pr-word-problem: that asks for one explicit group beyond primitive recursion; this stays inside PSPACE and shows the tower method cannot answer it, while climbing exactly one alternation per level.
  automatic-actor-twisted-brin-thompson-groups-have-pspace-wp: that caps twisted Brin-Thompson groups over synchronous rational actors at PSPACE and at coNP for actors with orbit problem in P; this shows the clopen actors are not in that easy class, since their orbit problems are Pi_k^p-hard.
---

**ESTABLISHED** by `twisted-brin-thompson-towers-pi-k-hardness-proof` (lane proof, belief-breaker
lane `swarm-0917-w18-w18-bh-break`, 2026-09-19; unreviewed).

## Statement

Let `G_0` be the trivial group acting on `S_0 = {1,2}`. For `k >= 0` put

- `G_(k+1) = SV_(G_k)`, the twisted Brin--Thompson group of the action of `G_k` on `S_k`;
- `S_(k+1) = Ω_(k+1)`, the set of proper nonempty clopen subsets of the Cantor cube `C^(S_k)` of
  `G_(k+1)`, with the natural action of `G_(k+1)`.

So `G_1 = 2V`, `G_2` is `SV_(2V)` over the clopen subsets of `C^2`, and so on. Then for every `k >= 1`:

1. `G_k` is finitely presented and simple, and `G_k` acts on `S_k` with type (A);
2. the word problem of `G_k` is `Π_k^p`-complete under polynomial-time many-one reductions;
3. the orbit problem `OP(G_k, S_k)` (word problem plus membership in the stabilizer of one fixed clopen
   set, the action being transitive) is `Π_k^p`-complete as well.

Both statements hold over every finite generating set.

## What changes

- **Every level of the polynomial hierarchy is the exact word-problem complexity of an explicit
  finitely presented simple group, unconditionally.** Before this node, the graph's rung table
  (`fp-simple-group-with-pspace-complete-word-problem`) read coNP (`nV`, unconditional), then
  coNP^⊕P (`(L ⊗ L)^x`, simplicity and finite presentation conditional), then PSPACE (open). Also,
  `bh-separators-must-omit-nested-decidable-hosts` §3 names `nV` as the hardest determined case.
- **Towers are not tame; they cost exactly one alternation.** The iteration clause of
  `twisted-brin-thompson-wp-equals-actor-orbit-problem` gave only an upper bound (one exponential per
  level, "elementary"). The truth is sharper in both directions:
  - a level adds exactly one quantifier alternation;
  - a finite tower over an actor with orbit problem in `Π_j^p` stays in `Π_(j+m)^p ⊆ PSPACE`.
- **Consequence for embeddings (conditional on PH not collapsing).** A word-problem embedding
  transfers by length-linear substitution. So if `Π_k^p ≠ Π_(k-1)^p`, then `G_k` embeds in no
  finitely generated group whose word problem lies in `Π_(k-1)^p`. In particular, `G_k` embeds in no
  rung-1 host (`nV`, or `FV(H_1, ..., H_n)` with coefficients in P), and `G_2` does not embed in `nV`
  unless `NP = coNP`.
- **What it does not do.** It does not settle `fp-simple-group-with-pspace-complete-word-problem`: no
  single `G_k` is PSPACE-hard unless `PH` collapses to its `k`-th level. The length of the hardness
  reduction grows like `4^k`, so the tower gives no uniform PSPACE-hardness. It does not touch
  `fp-simple-groups-with-arbitrarily-complex-word-problem` either: the whole tower lies in PSPACE.

## Mechanism (one line)

A twisted Brin--Thompson group can run a polynomial-size family of actor elements `g_d`, indexed by
binary strings `d` written on one coordinate, and a commutator test lights up exactly the boxes where
`g_d` fixes a point. So `w ≠ 1` iff `∃d  g_d ∈ Stab(s)` (existential amplification). A clopen set
spanning a family of boxes turns "`w` preserves it" into a universal statement (universal
amplification). This is the next actor's stabilizer problem, one level up. The base is a reversible
circuit acting on the digits of `2V`, as in Birget.

## Credit and novelty

- The groups: Belk--Zaremsky (arXiv:2001.04579). Finite presentation: Zaremsky (arXiv:2405.18354).
  The coNP-completeness of `2V`: Birget (arXiv:1902.03852). Birget's circuit encoding is the base case.
- Tower lower bounds were not found in a bounded check:
  - the graph (searches for tower, polynomial hierarchy, `Π_k` and twisted Brin--Thompson hardness);
  - a web search for polynomial-hierarchy-complete word problems of finitely presented simple groups.

  The result is treated as new here, and unreviewed.
