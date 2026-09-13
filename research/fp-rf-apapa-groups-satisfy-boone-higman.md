---
rg: 2
id: fp-rf-apapa-groups-satisfy-boone-higman
kind: claim
title: Finitely presented residually finite groups in the variety A_p^2 A embed in finitely presented simple groups
distinct_from:
  fp-residually-finite-boone-higman: that is Problem 5.3(12), every finitely presented residually finite group; this restricts to groups lying in the product variety A_p^2 A (elementary abelian p-groups by elementary abelian p-groups by abelian), a strictly smaller class.
  fp-metabelian-groups-satisfy-boone-higman: that is the metabelian variety A^2, whose finitely generated members have easy word problems; this is the next product variety, A_p^2 A, which already contains finitely presented residually finite groups with arbitrarily hard word problems.
  boone-higman-conjecture: that quantifies over all finitely generated groups with solvable word problem; this only over finitely presented residually finite groups in A_p^2 A.
artifacts:
  - research/artifacts/bh-complex-wp-apapa-reduction-2026-09-13.md
---

**OPEN.** Let `p` be a prime and let `A_p^2 A` be the product variety of
groups `G` with a normal series `1 <= T <= N <= G` where `T` and `N/T` are
abelian of exponent `p` and `G/N` is abelian. Every finitely presented
residually finite group in `A_p^2 A` embeds in a finitely presented simple
group.

## Why this class

- It is a special case of `fp-residually-finite-boone-higman`, by
  `fp-rf-apapa-bh-from-fp-rf-boone-higman`.
- It is the first rung above the metabelian case where Boone--Higman carries
  complexity. Kharlampovich--Myasnikov--Sapir (arXiv:1204.6506v5, §1.6, read
  from the PDF text 2026-09-13) say of their construction: "our group is a split
  extension of an elementary Abelian group of prime exponent by a metabelian
  group. Since every metabelian group has easy word problem and is residually
  finite, we can concentrate only on the elementary Abelian subgroup". So a
  Boone--Higman theorem for metabelian inputs, such as
  `fp-metabelian-groups-satisfy-boone-higman`, never forces a hard simple host.
- Their Theorem 4.19 (same source, pp. 26--27, verbatim): "For every recursive
  function f there exists a finitely presented residually finite group G from
  A2p A ∩ ZN3 A such that ρG (n) > f (n) for all n. In addition, we can assume
  that the word problem in G is as hard as the membership problem for any
  prescribed recursive set of natural numbers."
- By `complex-fp-simple-groups-from-apapa-rf-boone-higman`, this claim implies
  the OPEN root `fp-simple-groups-with-arbitrarily-complex-word-problem`. The
  root is the only complexity consequence of Boone--Higman recorded here, so this
  class is where a counterexample from word-problem complexity alone would have
  to live, and a proof for this class would remove that possibility.

## What is known about the class

- The hard examples are split extensions `T ⋊ (H_1^(H_2) ⋊ H_2)` with `T` and
  `H_1^(H_2)` elementary abelian of exponent `p` and `H_2` abelian (§4.1 of the
  source, Lemmas 4.4 and 4.5). The quotient `H_1^(H_2) ⋊ H_2` is finitely
  generated metabelian, so it lies in B_A by
  `fp-metabelian-groups-satisfy-boone-higman`. All the difficulty sits in the
  exponent-`p` module `T`, whose basis is indexed by configurations of a Minsky
  machine (Lemma 4.14).
- No hard group in this class is known to embed in a finitely presented simple
  group, a finitely presented self-similar group, or a group with a type (A)
  action. The quasi-linear route of the metabelian case cannot reach them: every
  finitely generated linear group has a logspace word problem, so their hosts
  share one recursive bound (`complexity-bounded-host-classes-are-not-universal`).

## Attempts

1. **Translation virtual endomorphism on the configuration module.** For a
   faithful self-similar action, and then Zaremsky's theorem
   (`fp-self-similar-groups-embed-in-fp-simple-groups`), it would suffice to find
   a finite-index subgroup `Q_1` and a homomorphism `Q_1 -> G` with trivial core.
   The natural candidate shifts every counter of a configuration down by a
   constant on the finite-index normal subgroup `T(V_R)` of Lemma 4.15 and fixes
   the metabelian letters. Minsky add and subtract commands commute with that
   shift, but zero tests do not, and in the construction the zero-status bits are
   carried by the `A`-letters (relations G5 and G8). So the map is not a
   homomorphism. *Dies as stated.* Machines whose zero tests are invisible to the
   shift were not examined.
