---
rg: 2
id: thompson-f-amenable-iff-group-ring-is-ore
kind: claim
title: Thompson's group F is amenable iff its group ring over a field is an Ore domain
distinct_from:
  kaplansky-zero-divisor-conjecture: that asks for zero divisors in group rings of torsion-free groups; this uses the known absence of zero divisors for F to turn amenability into the Ore condition.
---

**ESTABLISHED by citation plus standard facts.** For a field `K`, `F` is amenable
iff `K[F]` is an Ore domain: every two nonzero elements `a, b` have nonzero
`u, v` with `au = bv`, and symmetrically on the other side.

Derivation:
1. **Kielak's criterion.** The appendix by D. Kielak to L. Bartholdi and D.
   Kielak, *Amenability of groups is characterized by Myhill's Theorem*,
   arXiv:1605.09133v2 (7 Jun 2016). From the abstract, verbatim: the appendix
   "proves that group rings without zero divisors are Ore domains precisely when
   the group is amenable, answering a conjecture attributed to Guba".
2. **No zero divisors in `K[F]`.** `F` acts faithfully by orientation-preserving
   homeomorphisms of the open interval `(0,1)`, which is homeomorphic to `R`, so
   `F` is left-orderable. Group rings of left-orderable groups over a field have
   no zero divisors, because left-orderable groups have unique products. These
   facts are standard.

**Consequence.** Deciding amenability of `F` is equivalent to deciding the Ore
condition in `K[F]`. A single pair `a, b` with no nonzero common multiple would
prove `thompson-f-is-not-amenable`. Guba's survey (arXiv:2305.07113) says it
studies equations in the group ring of `F`; only its abstract has been read into
this graph.

Scope: Kielak's statement is taken from the arXiv abstract page (read
2026-09-12). The precise hypotheses on the coefficient ring were not re-read;
the claim is scoped to fields, where step 2 applies.

Citation route: `thompson-f-ore-criterion-citation`.
