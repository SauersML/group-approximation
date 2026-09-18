---
rg: 2
id: fpbs-amenable-quotient-normal-relative-threshold-is-pc
kind: claim
title: Converse percolation Kesten, a normal subgroup with amenable quotient has relative threshold equal to p_c
distinct_from:
  fpbs-percolation-kesten-normal-gap: that asks for a strict relative gap when the quotient is nonamenable and is OPEN; this proves the converse, no gap when the quotient is amenable, so that claim becomes the only possible direction and the gap is equivalent to nonamenability of the quotient whenever it holds.
  fpbs-relative-threshold-commensurability-invariant: that kills relative routes along finite-index subgroups by commensurability; this kills them along every subgroup containing an infinite normal subgroup with amenable quotient, which includes infinite-index subgroups.
  fpbs-quotient-spectral-dt-certificates-are-subgroup-blind: that shows one certificate family never gains from an amenable subgroup; this shows the relative threshold itself collapses to p_c for every subgroup of amenable normal-quotient type, whatever method is used.
  fpbs-amenable-normal-fibre-mass-maximal-at-subgroup: that bounds coset fibre masses by the subgroup mass for an amenable subgroup; this concerns a normal subgroup with amenable quotient, the opposite amenability hypothesis, and compares thresholds.
  fpbs-hp-relative-burton-keane: that is Hutchcroft--Pan's relative uniqueness theory; this is a threshold equality proved with a relative Burton--Keane count over invariant Folner cells of the quotient.
---

**ESTABLISHED.**

**Setting.** Let `Gamma` be a finitely generated group, `S` a finite symmetric
generating set, `G = Cay(Gamma,S)`, and `p_c(I;G)` the Hutchcroft--Pan relative
critical threshold of a subgroup `I`: the infimum of `p` at which a cluster
meeting `I` in infinitely many vertices exists almost surely.

**Theorem.** Let `N` be an infinite normal subgroup of `Gamma` such that
`Q = Gamma/N` is amenable. Then

```text
p_c(N;G) = p_c(G).
```

**Corollaries.**

1. **Blind subgroups.** Let `I <= Gamma` be a subgroup whose normal core
   `core(I) = intersection of g I g^(-1)` is infinite and has amenable quotient
   `Gamma/core(I)`. Then `p_c(I;G) = p_c(G)`, and `chi^I_p = infinity` for every
   `p > p_c(G)`. So condition 1 of
   `fpbs-relative-gap-along-any-subgroup-separates` fails for `I` on every
   Cayley graph. (A `core(I)`-infinite cluster is `I`-infinite, so
   `p_c(I;G) <= p_c(core(I);G)`.)
2. **The percolation Kesten gap is an iff where it holds.** If
   `p_c(G) < p_c(N;G)` for an infinite normal `N`, then `Gamma/N` is
   nonamenable. So `fpbs-percolation-kesten-normal-gap` is the statement
   "for infinite normal `N`, `p_c(G) < p_c(N;G)` iff `Gamma/N` is nonamenable".
3. **Obstruction on the normally co-amenable class.** If `Gamma` is normally
   co-amenable (`fpbs-normally-coamenable-class-nonuniqueness`), every subgroup
   with infinite normal core is blind. So any relative-threshold proof of
   `p_c < p_u` on that class must use a subgroup with finite normal core. In a
   simple group that means a subgroup with trivial core, i.e. a faithful
   coset action. The invariant is amenability of `Gamma/core(I)`, and every
   such route dies at condition 1 of the separation criterion.

**What is not claimed.** The case of a non-normal `H` with co-amenable
`H\Gamma`, or with finite core, is not covered. The proof needs an invariant
random partition of the coset space into finite cells with small boundary, and
that construction uses the group structure of `Q`.

Proof: `fpbs-amenable-quotient-normal-relative-threshold-is-pc-proof`.
