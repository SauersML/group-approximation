---
rg: 2
id: weinbaum-proper-subwords-of-relator-nontrivial-citation
kind: route
title: Import Weinbaum's subword theorem as stated in Linton, arXiv:2407.09272v2, Theorem 3.1
target: weinbaum-proper-subwords-of-relator-nontrivial
requires: []
artifacts:
  - research/artifacts/fpbs/docs/dual-forest-morse-matching-one-relator.md
---

Literature import, credited in full.

C. M. Weinbaum, *On relators and diagrams for groups with one defining
relation*, Illinois J. Math. 16 (1972), 308-322. The statement was read on
2026-09-17 from the arXiv HTML rendering of M. Linton, *Residually rationally
solvable one-relator groups*, arXiv:2407.09272v2, Theorem 3.1, through an
automated fetch:

> If F is a free group, w∈F is a word and G=F/⟨⟨w⟩⟩ is a one-relator group,
> then every proper non-empty subword of w is non-trivial in G.

The fetch may have dropped a standing hypothesis that `w` is cyclically
reduced. The claim assumes it, so either reading supports the claim. The
original paper was not re-read, and nothing here reproves the theorem.

The extension to cyclic subwords is immediate: a cyclic permutation of `r` is
again cyclically reduced and has the same normal closure.
