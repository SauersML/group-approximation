---
rg: 2
id: linton-radical-has-a-short-weinbaum-marker
kind: claim
title: Every nontrivial torsion-free Linton radical contains a nontrivial proper subword of the defining relator
distinct_from:
  one-relator-fox-magnus-descent-to-derived-linton-radical: that separates every element outside `R'` by a mod-k Fox--Magnus quotient; this produces an explicit short element inside `R`, and inside `R'` in the perfect case, which the canonical quotient necessarily loses.
  linton-radical-abelianization-is-truncated-group-ring: that computes the whole first-order module `R/R'`; this is a word-length and inequation statement giving a representative of the hidden radical directly in the original relator spelling.
  nonsofic-one-relator-relator-has-primitivity-rank-two: that constrains the primitivity rank of a hypothetical counterexample; this identifies a proper-subword witness in the Linton radical of every non-residually-rationally-solvable torsion-free presentation, whether or not the group is sofic.
artifacts:
  - research/artifacts/one-relator-weinbaum-gate-and-berlai-calibration-2026-08-30.md
---

Let `G=F/<<w>>` be torsion-free, with `F=A*B` a splitting into free factors
for which the fixed spelling of `w` is cyclically reduced of syllable length at
least two.  Let

    R = G_Q^(omega),       pi : G -> H=G/R

be Linton's canonical radical and quotient.  If `R != 1`, then some proper
nonempty contiguous subword `u` of `w` satisfies

    u != 1 in G,           pi(u)=1 in H.

Thus `u` is a nontrivial element of `R` represented by a word strictly shorter
than the defining relator.  When Linton's integer is `k=1`, so that `R=R'` is
perfect, the same `u` lies in the derived core missed by first-order
Fox--Magnus descent.

The marker is algorithmically findable from the presentation using Linton's
algorithm for the canonical quotient and the one-relator word problem.
