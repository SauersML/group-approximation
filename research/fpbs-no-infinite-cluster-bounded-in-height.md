---
rg: 2
id: fpbs-no-infinite-cluster-bounded-in-height
kind: claim
title: On a Cayley graph with a homomorphism to Z, no infinite Bernoulli cluster is bounded above or below in height, so the level-reach probability never drops below theta
distinct_from:
  fpbs-co-amenable-subgroup-relative-threshold-is-pc: that proves infinite expected intersection with a co-amenable subgroup above p_c, via trifurcations and Folner sets of the Schreier graph; this proves a pathwise statement at every p, for every infinite cluster, via one finite-energy flip and a mass transport on the top set, and needs neither p > p_c nor any Folner set.
  fpbs-layer-renewal-along-homomorphism-is-critical-l2: that kills renewal with full-band coefficients; this is the pathwise input that kills the half-space survivor it leaves (fpbs-half-space-first-entry-renewal-dies-at-level-reach).
  fpbs-boundary-tilted-susceptibility-kernel: that works with boundary Busemann heights, which are invariant only under a possibly nonunimodular end stabilizer; this needs a height whose differences are invariant under the whole unimodular group, and it is false for the Busemann height of the end-fixing tree.
artifacts:
  - research/fpbs-no-infinite-cluster-bounded-in-height-proof.md
---

**ESTABLISHED.** Proof route: `fpbs-no-infinite-cluster-bounded-in-height-proof`.

**Setting.**
- `Gamma` is finitely generated, `S` is a finite symmetric generating set, and
  `G = Cay(Gamma,S)` has edges `{x, xs}`. `o = 1`.
- `h : Gamma -> Z` is a nonzero homomorphism, and `K = max_(s in S) |h(s)|`.
- `U_n = {x : h(x) >= n}` is the upper half-space at level `n`, and
  `L_n = {x : h(x) < n}` the lower one.
- `omega` is Bernoulli(`p`) bond percolation, `p in (0,1)`, `K_x` is the
  open cluster of `x`, and `theta(p) = P_p(|K_o| = infinity)`.

**Theorem.** For every `p in (0,1)`, almost surely:

1. **No bounded-height cluster.** No infinite cluster is bounded above in
   `h`, and no infinite cluster is bounded below in `h`.
2. **Infinitely many crossings.** Every infinite cluster has infinitely many
   open edges between `L_n` and `U_n`, for every `n`.
3. **Half-space components leak.** Every infinite component of the open
   subgraph induced on `L_n` has infinitely many open edges into `U_n`.
   The same holds for `U_n` with edges into `L_n`.

**Corollary (level reach).** For every `n in Z` and every `p`:

```text
P_p(o <-> U_n) >= theta(p).
```

This holds because `K_o` infinite implies `K_o ∩ U_n ≠ ∅`, by item 1.

**Scope.**
- The proof uses only three things:
  - invariance of the height differences `h(y) - h(x)` under the whole
    group, which holds because `h` is a homomorphism;
  - unimodularity, which holds for every Cayley graph;
  - finite energy on finite edge sets.

  So it holds verbatim for every `Gamma`-invariant bond percolation with
  finite energy, for example the random-cluster model.
- No amenability or nonamenability assumption is used, and no assumption
  `p > p_c`. Below `p_c` the statement is vacuous.

**Calibration: unimodularity is essential.** On the `3`-regular tree, take the
Busemann height `b_xi` of an end `xi`. Its differences are invariant only
under the end stabiliser `Aut_xi(T)`, which is nonunimodular. For
`p in (1/2, 1)`, every infinite cluster has exactly one highest vertex, the
point where its path toward `xi` is first closed. So every infinite cluster
is bounded above, with a top set of size one. The proof dies at exactly one
step: the mass transport of Step 1 of the route, which needs unimodularity.
The flip of Step 2 goes through on the tree unchanged. So heights coming from
boundary cocycles of nonunimodular end stabilisers are outside the scope of
this lemma, and the level-reach corollary is false for them.

## Attempts
