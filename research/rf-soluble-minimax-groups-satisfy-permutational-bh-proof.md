---
rg: 2
id: rf-soluble-minimax-groups-satisfy-permutational-bh-proof
kind: route
title: Pyber--Segal make the group linear in characteristic zero, and finitely generated linear groups over fields lie in B_A
target: rf-soluble-minimax-groups-satisfy-permutational-bh
requires:
  - rf-soluble-finite-rank-groups-are-char-zero-linear
  - quasi-linear-groups-satisfy-permutational-boone-higman
---

Lane `bh-solvable`, 2026-09-18. Let `G` be finitely generated, virtually soluble,
residually finite and of finite Prüfer rank.

1. **Linearity.** By `rf-soluble-finite-rank-groups-are-char-zero-linear`
   (Pyber--Segal, arXiv:0711.0687, Theorem 1.1 and Corollary 1.3, read at source,
   plus induction from a soluble subgroup of finite index), `G ≤ GL_n(K)` for some
   field `K` of characteristic `0`.
2. **Permutational Boone--Higman.** `G` is a finitely generated group of matrices over
   one field, so `quasi-linear-groups-satisfy-permutational-boone-higman` (reviewed
   PASS, `research/artifacts/review-metabelian-bh-2026-09-13.md`), with one factor,
   puts `G` in `B_A`.
3. **Conclusion.** Groups in `B_A` have solvable word problem and embed in finitely
   presented simple groups (part 3 of
   `boone-higman-type-a-class-closed-under-finite-extensions`, through Zaremsky's
   Theorem 1.1). ∎

**Alternative for the last step.** `char-zero-linear-groups-satisfy-boone-higman`
(reviewed) gives the finitely presented simple envelope directly, without `B_A`.

**What was checked at source.** Only the Pyber--Segal statements quoted in the
linearity node. The equivalence "finite rank ⟺ minimax" and the list of equivalent
conditions for minimax groups are the paper's own summary of Lennox--Robinson Ch. 5,
which was not read here; the statement of this route does not depend on them, since it
is phrased with "finite rank" and "residually finite", the exact hypotheses of
Theorem 1.1.
