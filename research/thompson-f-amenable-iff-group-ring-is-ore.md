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
   arXiv:1605.09133v2 (7 Jun 2016). Its theorem, read from the LaTeX source: "Let
   `G` be a group, and let `K` be a field such that `K G` has no zero divisors. Then
   `G` is amenable if and only if `K G` is an Ore domain."
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

Scope: the source's only hypotheses are that `K` is a field and `K G` has no zero
divisors, and step 2 supplies the second for every field. The appendix's proof of
the hard direction was read (2026-09-12); it rests on Bartholdi's main theorem and
the flatness of the classical field of fractions, as recorded in the citation route.
Left and right Ore conditions agree for group rings through `g -> g^-1`.

Citation route: `thompson-f-ore-criterion-citation`.
