---
rg: 2
id: leavitt-path-algebras-are-steinberg-algebras
kind: claim
title: Every Leavitt path algebra over a commutative unital ring is the Steinberg algebra of its graph groupoid, so the binary Leavitt algebra is the Steinberg algebra of the Cuntz groupoid
distinct_from:
  full-group-units-embed-in-steinberg-algebras: that embeds the topological full group of an ample groupoid in the units of its Steinberg algebra; this identifies Leavitt path algebras themselves as Steinberg algebras, which puts the non-MF coefficient ring into the Steinberg-algebra dictionary.
---

**ESTABLISHED (import).** For every directed graph `E` and every commutative unital ring `R`, the Leavitt
path algebra `L_R(E)` is isomorphic to the Steinberg algebra `A_R(G_E)` of the graph groupoid `G_E`
(Clark–Sims, arXiv:1311.3701, Example 3.2).

**Specialisation used by the UN program.**
- Take `E = R_2`, the rose with one vertex and two loops `e_1, e_2`.
- The non-MF presentation `L_k(1,2) = k<s_1,s_2,t_1,t_2 | t_i s_j = delta_ij, s_1 t_1 + s_2 t_2 = 1>` is
  `L_k(R_2)` under `s_i = s_(e_i)`, `t_i = s_(e_i^*)`. These are the Cuntz–Krieger relations (CK1) and (CK2)
  at the single vertex.
- `G_(R_2)` is the Cuntz groupoid of the one-sided full shift on `{1,2}^N`.
- So `L_k(1,2) ≅ A_k(G_(R_2))` for every field `k`, including `F_2`.

**Role.** This is the paradox end of the dictionary in `research/artifacts/un-blueprint-2026-09-13-part1.md`
§2. The measure end is `crossed-products-are-transformation-steinberg-algebras`.

**Review (un-verify-3, 2026-09-13): PASS.** The quoted Example 3.2 matches arXiv:1311.3701 TeX lines 285–299 (label `ex:lpa`) verbatim. The rose specialization is checked: (CK1) `t_i s_j = δ_ij` and (CK2) `Σ s_i t_i = 1` at the single vertex give `L_k(1,2) = L_k(R_2)`. `research/artifacts/un-review3-2026-09-13-part1.md` §9.
