---
rg: 2
id: twisted-bt-type-fn-necessity-citation
kind: route
title: Import FFWZ Definition 1.3, Proposition 4.17 and Corollary 4.18
target: twisted-brin-thompson-type-fn-implies-type-an
requires: []
---

Source: F. Fournier-Facio, X. Wu, M. C. B. Zaremsky, *Abstract twisted Brin--Thompson
groups*, arXiv:2603.24687v2. Read 2026-09-18 from the PDF text extracted on MSI,
`/scratch.global/sauer354/bh-reviewer/2603.24687.txt` (line numbers refer to that file).

- **Definition 1.3, lines 83–91.** "For n ∈ N, we say the action is of type [A_n] if the
  following hold: (i) G is of type F_n. (ii) For any finite T ⊆ S, Stab_G(T) is of type
  F_{n−|T|}. (iii) The diagonal action of G on S^n has finitely many orbits. ... If an
  action of type [A_n] (with n ∈ N ∪ {∞}) is moreover faithful, we say that it is of type
  (A_n)."
- **Proposition 4.17, lines 1107–1166.** For `G ↷ S` of type `[A_1]`, `Z ≀_S G` is a
  quasi-retract of `SV_G`.
- **Type [HA_n], lines 1167–1171.** "Say G ↷ S is of type [HA_n] if G is of type FP_n,
  Stab_G(T) is of type FP_{n−|T|} for all finite T ⊆ S, and the diagonal action of G on
  S^n has finitely many orbits. Then Z ≀_S G is of type FP_n if and only if G ↷ S is of type
  [HA_n] [BdCK15]."
- **Corollary 4.18, lines 1172–1181.** "For any n ≥ 1, if SV_G is of type F_n, then
  G ↷ S is of type [A_n]. In particular if SV_G is finitely presented then G ↷ S is of type
  [A_2]. Similarly for type FP_n and type [HA_n]." The proof combines Proposition 4.17,
  Alonso's quasi-retraction theorem, and [dC06, BdCK15].

The case `n = 1` needs `[A_1]` as a hypothesis of Proposition 4.17. That hypothesis holds
because `SV_G` finitely generated forces `[A_1]` (their Theorem 4.1(i), line 748). The statements
were read in full; the proof of Proposition 4.17 was read but not re-checked line by line.
