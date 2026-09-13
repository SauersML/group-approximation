---
rg: 2
id: kms-hard-fp-rf-groups-lie-in-apapa-variety-citation
kind: route
title: Import the variety statement for the Minsky-machine groups of Kharlampovich-Myasnikov-Sapir
target: kms-hard-fp-rf-groups-lie-in-apapa-variety
requires: []
artifacts:
  - research/artifacts/bh-complex-wp-apapa-reduction-2026-09-13.md
---

Source: Kharlampovich--Myasnikov--Sapir, *Algorithmically complex residually
finite groups*, Bull. Math. Sci. **7** (2017), 309--352, DOI
10.1007/s13373-017-0103-z, read from the PDF text 2026-09-13. The arXiv version
arXiv:1204.6506v5 was read too.

1. **The hard groups.** Theorem 4.21 (p. 345), verbatim: "For every recursive set
   of natural numbers X and every recursive function g(n) there exists a finitely
   presented residually finite solvable of class 3 group G such that the word
   problem in G is as hard as the membership problem in X and polynomially
   reduces to it; the Dehn function G is bigger than g(n)." Its proof: "The first
   statement now follows from Theorems 4.18 and 3.9." So the group is one of the
   Minsky-machine groups `G(MM_k)` of §4.1.
2. **Residual finiteness of those groups.** Theorem 4.18 (p. 343), verbatim: "If a
   Minsky machine MM k is sym-universally halting then the group G(MM k ) is
   residually finite. The word problem in G(MM k ) and the configuration
   equivalence problem for MM k are polynomially reducible to each other."
3. **The variety.** Theorem 4.3(a) (p. 335), verbatim: "The group G(MM k ) belongs
   to A2p A ∩ ZNk+1 A." After Lemma 4.5 (p. 337): "By construction, the group G is
   a semidirect product of T and the metabelian group H1H2 ⋊ H2 . By Lemma 4.4, G
   is solvable of class 3 and, moreover, belongs to A2p A."
4. **Independent confirmation in the arXiv version.** arXiv:1204.6506v5, Theorem
   4.19 (pp. 26--27), verbatim: "For every recursive function f there exists a
   finitely presented residually finite group G from A2p A ∩ ZN3 A such that ρG (n)
   > f (n) for all n. In addition, we can assume that the word problem in G is as
   hard as the membership problem for any prescribed recursive set of natural
   numbers."
5. **The quantitative sense.** Definition 2.2(a) (p. 319), verbatim up to one
   symbol lost in extraction: "We say that an algorithmic problem A is as hard as
   an algorithmic problem B if for any decision algorithm for A which solves the
   problem in time T A there exists an algorithm for B that solves it in time
   [≼] T A." That is the relation `(KMS1)` already imported in
   `kms-arbitrarily-hard-fp-rf-groups`, which fixes the constant form used there.

Items 1--3 together give `(KMSV1)`. The recursive membership problem `X` of the
claim is a recursive set of natural numbers, as in Theorem 4.21. The encoding
convention matches the one `kms-arbitrarily-hard-fp-rf-groups` uses. `∎`
