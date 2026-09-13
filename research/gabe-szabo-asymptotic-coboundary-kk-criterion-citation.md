---
rg: 2
id: gabe-szabo-asymptotic-coboundary-kk-criterion-citation
kind: route
title: Gabe--Szabó arXiv:2205.04933v3 Definition 5.9, Corollary 5.11, Notation 5.13, Theorem 5.14 and Remark 6.5
target: gabe-szabo-asymptotic-coboundary-kk-criterion
requires: []
---

**Source read 2026-09-13.**  J. Gabe and G. Szabó, *The dynamical
Kirchberg–Phillips theorem*, arXiv:2205.04933v3 (16 Aug 2023), Acta Math. 232.
Read from the ghostscript text extraction on MSI
(`/scratch.global/sauer354/ex/ex-uct-detection-phantom/2205.04933.sq3`,
lines 3012–3087 and 3230–3242).  Subscripts were flattened by the
extraction and are restored below.

- **Definition 5.9** (cf. [100, Definition 1.4]). "Let G be a second-countable,
  locally compact group. Let B be a C∗-algebra and β : G ↷ B an action. We say
  that a norm-continuous cocycle u : G → U(1+B) is an asymptotic coboundary,
  if there exists a continuous path of unitaries v : [0,∞) → U(1+B) such that
  lim_{t→∞} max_{g∈K} ‖u_g − v_t β_g(v_t)^∗‖ = 0 for every compact set K ⊆ G."
- **Corollary 5.11.** "Let G be a compact group and β : G ↷ B an action on a
  C∗-algebra. If a norm-continuous β-cocycle u : G → U(1+B) is an asymptotic
  coboundary, then it is a coboundary."  It rests on Proposition 5.10 (Izumi,
  [54, Lemma 2.4]): a cocycle with max_g ‖u_g − 1‖ < 1 is a coboundary.
- **Notation 5.13.** "Given a unital C∗-algebra A, we will denote by ι_A : C → A
  the canonical unital inclusion. If A carries a group action, we will equip C
  with the trivial action so that ι_A can be viewed as an equivariant
  inclusion."
- **Theorem 5.14.** "Let β : G ↷ B be an amenable and isometrically
  shift-absorbing action on a Kirchberg algebra and let u : G → U(1+B) be a
  β-cocycle.
  (i) Suppose β is strongly stable. If (u, 1) ∼_h (1, 1) in the sense of
  Definition 1.9, then u is an asymptotic coboundary, and in fact there exists
  a norm-continuous path y : [0,∞) → U(1+B) with y_0 = 1 and
  lim_{t→∞} max_{g∈K} ‖u_g − y_t β_g(y_t)^∗‖ = 0 for every compact set K ⊆ G.
  (ii) Suppose G is exact and B is unital. Consider the element
  u^♯ = KK^G(ι_B, u) ∈ KK^G(id_C, β) associated to u. Then u is an asymptotic
  coboundary if and only if u^♯ = KK^G(ι_B, 1)."
- **Proof of (ii), as printed.** "We observe by comparing definitions that u is
  an asymptotic coboundary if and only if the two unital cocycle embeddings
  (ι_B, 1), (ι_B, u) : (C, id) → (B, β) are asymptotically unitarily
  equivalent. This is seen to be equivalent to u^♯ = KK^G(ι_B) by applying
  Theorem 5.8 to A = C."
- **Remark 6.5** (excerpt). "Given a β-cocycle u : G → U(B), we consider the
  KK^G-equivalence in KK^G(β^u, β) induced by the exterior equivalence
  (id_B, u) : (B, β^u) → (B, β). By Theorem 5.14, the extra condition
  u^♯ = KK^G(ι_B) holds if and only if u is a coboundary, which holds if and
  only if this element can also be represented by a conjugacy. In some very
  special cases, such as when β has the Rokhlin property, it may happen that
  all cocycles are coboundaries, but in general this provides plenty of
  examples demonstrating that conjugacy between actions on unital Kirchberg
  algebras is indeed stronger than cocycle conjugacy."

**Quoted in the peer import and not re-quoted here.**  Proposition 3.15
(isometric shift-absorption is pointwise outerness on Kirchberg algebras),
Theorem 5.8 and Definition 1.15, in `gabe-szabo-unital-uniqueness-theorem-citation`.
