---
rg: 2
id: infinite-left-orderable-kazhdan-group-from-circle
kind: route
title: An infinite Kazhdan group of circle homeomorphisms lifts, virtually or centrally, to an infinite Kazhdan group of line homeomorphisms
target: infinite-left-orderable-kazhdan-group
requires: [infinite-kazhdan-group-of-circle-homeomorphisms, kazhdan-circle-group-lift-dichotomy]
artifacts:
  - research/artifacts/kazhdan-circle-group-lift-dichotomy-2026-09-16.md
---

**Standard inputs** (Bekka--de la Harpe--Valette, *Kazhdan's Property (T)*, Theorem
1.7.1, re-read 2026-09-16). A subgroup of finite index in a discrete group has property
(T) if and only if the group does.

**Lemma (line groups are left-orderable).** Every subgroup of `Homeo_+(R)` is
left-orderable.

*Proof.* Enumerate `Q = {q_1, q_2, …}`. Distinct homeomorphisms `F ≠ H` differ at some
rational, by continuity. Let `n = n(F,H)` be the least index with `F(q_n) ≠ H(q_n)`, and
declare `F ≺ H` iff `F(q_n) < H(q_n)`.

- *Totality.* For any `F, H`, exactly one of `F ≺ H`, `F = H`, `H ≺ F` holds.
- *Transitivity.* Let `F ≺ H ≺ L`, with `a = n(F,H)` and `b = n(H,L)`. At index
  `min(a,b)`, all earlier values agree. The strict inequality at that index persists:
  - if `a < b`, then `F(q_a) < H(q_a) = L(q_a)`;
  - if `b < a`, then `F(q_b) = H(q_b) < L(q_b)`;
  - if `a = b`, then both inequalities are strict.

  So `F ≺ L`.
- *Left invariance.* For `M ∈ Homeo_+(R)`, injectivity gives `n(MF, MH) = n(F,H)`, and
  monotonicity preserves the inequality.

∎

**Proof of the route.** Let `G ⊂ Homeo(S^1)` be an infinite Kazhdan group, as provided
by `infinite-kazhdan-group-of-circle-homeomorphisms`. Put
`G_+ := G ∩ Homeo_+(S^1)`. It is the kernel of the orientation character, so
`[G : G_+] ≤ 2`. Hence `G_+` is infinite and Kazhdan (Theorem 1.7.1).

Apply `kazhdan-circle-group-lift-dichotomy` to `G_+`, with
`Ĝ_+ = p^{-1}(G_+) ⊂ Homeo_Z(R) ⊂ Homeo_+(R)`.

- **Case (A).** Some `K̂ ⊂ Ĝ_+` maps isomorphically onto a finite-index subgroup `K` of
  `G_+`.
  - `K` is infinite, and it is Kazhdan by Theorem 1.7.1.
  - `K ≅ K̂ ⊂ Homeo_+(R)`, so `K` is left-orderable by the Lemma.
- **Case (B).** `Ĝ_+` is Kazhdan.
  - It is a subgroup of `Homeo_+(R)`, so it is left-orderable by the Lemma.
  - It is infinite, since it contains the translation `T` of infinite order.

Either way some infinite left-orderable group has property (T). ∎

In case (B) the witness has infinite centre, containing `T`. This route gives no
reduction to witnesses with finite centre. Conversely, the shapes (A) and (B) are not
a normal form for witnesses of the target. Every line witness `H` already has shape (A)
through its one-point compactification: the lifts fixing the integers form a periodic
copy of `H` in `Homeo_Z(R)`.
