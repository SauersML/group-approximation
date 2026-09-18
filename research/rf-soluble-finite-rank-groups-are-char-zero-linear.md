---
rg: 2
id: rf-soluble-finite-rank-groups-are-char-zero-linear
kind: claim
title: Every finitely generated residually finite virtually soluble group of finite Prüfer rank is linear over a field of characteristic zero
distinct_from:
  char-zero-linear-groups-satisfy-boone-higman: that embeds finitely generated linear groups of characteristic zero in finitely presented simple groups; this is the linearity input that puts a group-theoretically defined soluble class inside that one.
  fg-metabelian-groups-embed-in-products-of-coprimary-quotients: that is Wehrfritz's quasi-linearity of finitely generated metabelian groups, of unbounded rank; this is linearity over one field for soluble groups of any derived length, but only of finite rank and residually finite.
artifacts:
  - research/artifacts/gq-bh-bh-solvable-status.md
---

**ESTABLISHED (literature import plus one elementary step).** The source was read in
its arXiv TeX (arXiv:0711.0687v1, fetched via MSI, copy at `gq/src/bh-solvable/`).
Not independently reviewed.

## Statement

Let `G` be a finitely generated group that is residually finite and virtually
soluble, and of finite Prüfer rank (every finitely generated subgroup is generated
by a bounded number of elements). Then `G` has a faithful finite-dimensional
representation over a field of characteristic `0`.

## Source

L. Pyber and D. Segal, *Finitely generated groups with polynomial index growth*,
J. reine angew. Math. 612 (2007), 173–211; arXiv:0711.0687. Theorem numbers from the
TeX counters (theorems, corollaries and propositions share one counter per section):

- **Theorem 1.1** (label `sol`): "Let `G` be a fg RF group that is virtually soluble.
  Then `G` has PIG if and only if `G` has finite rank."
- **Corollary 1.3** (label `lin`): "Let `G` be a fg group that is residually
  finite-soluble. If `G` has PIG then `G` is a linear group over a field of
  characteristic `0`." The paper says it follows from Theorem 1.2 and
  Mann–Segal, Proc. LMS (3) 61 (1990), Proposition 2.4 (not read here).
- **§3, recalled facts** (attributed there to Mal'cev, Robinson and Zaicev, with
  Lennox–Robinson, *The theory of infinite soluble groups*, Ch. 5, as reference; not
  read here): a finitely generated soluble group has finite rank if and only if it
  is minimax; and for a minimax group, being virtually torsion-free, having finite
  maximal periodic normal subgroup `τ(G)`, being residually finite, and being
  reduced are equivalent.

## Proof of the statement from the source

Let `N` be a soluble normal subgroup of finite index in `G`.
1. `N` is finitely generated, residually finite and of finite rank, so it has PIG by
   Theorem 1.1.
2. `N` is residually finite and soluble, so every finite quotient of `N` is soluble:
   `N` is residually finite-soluble. By Corollary 1.3, `N` has a faithful
   representation `ρ: N → GL_d(K)` with `char K = 0`.
3. The induced representation `Ind_N^G ρ` is faithful on `G`. An element outside `N`
   permutes the `[G:N]` blocks nontrivially, and an element of `N` acts block
   diagonally by conjugates of `ρ`, each faithful. So `G ≤ GL_(d[G:N])(K)`. ∎

## Equivalent hypotheses

By the recalled facts in §3 of the source, for a finitely generated virtually soluble
group "residually finite of finite rank" is the same as "virtually torsion-free
minimax". For example, `BS(1,n)`, Abels' groups `A_p ≤ GL_4(Z[1/p])`, and every
polycyclic group qualify.
