---
rg: 2
id: order-seeds-transfer-computable-orders
kind: claim
title: Order seeds make the order computable, and pass computable left orders to every subgroup that acts freely on some orbit point; so, by Darbinyan's and Harrison-Trainor's groups, absolute order seeds cannot seed every decidable left-orderable group, and question (O) needs an isolated order on a finitely presented group with a hard word problem
requires:
  - order-seeds-are-rigid-relative-seeds
  - seeded-recursively-presented-groups-have-solvable-word-problem
distinct_from:
  order-seeds-are-rigid-relative-seeds: that constructs order seeds and poses question (O); this bounds what they can reach, using the computability theory of orders.
  seeded-recursively-presented-groups-have-solvable-word-problem: that shows a seed makes its point computable; this reads that point, for an order seed, as a computable order and transfers it to subgroups.
---

**ESTABLISHED** (lane proof, bh-emitter-a, 2026-09-18; elementary given the cited theorems; not reviewed). The
cited results are credited below.

## Credits (the computability theory of orders used here)

- **A. Darbinyan, "Computability, orders, and solvable groups", J. Symbolic Logic (2020), arXiv:1909.05720.**
  Read on 2026-09-18 through the arXiv HTML rendering; statements are paraphrased closely.
  - *Theorem 1.* A two-generated bi-orderable computable group that does not embed in any countable group with a
    computable p-order relation. It answers Downey and Kurtz.
  - *Corollary 2.* A finitely presentable left-orderable group with decidable word problem and no computable left
    order. It combines Theorem 1 with the Bludov–Glass theorem below.
  - *Theorem 2.* A two-generated, recursively presented, bi-orderable solvable group with undecidable word
    problem. It answers Bludov and Glass's Kourovka question.
- **V. Bludov and A. Glass** (Proc. LMS 2009; recalled, as quoted by Darbinyan). Every left-orderable computable
  group embeds in a finitely presentable left-orderable group with decidable word problem.
- **M. Harrison-Trainor, "Left-orderable computable groups", J. Symbolic Logic (2018)** (recalled, not re-read). A
  computable left-orderable group with no computable left order.
- **A. Darbinyan and M. Steenbock, J. LMS (2022)** (recalled, not re-read). Every countable left-ordered group
  embeds in a finitely generated left-ordered simple group, computably when the order is computable. It also
  gives a Boone–Higman–Thompson-type theorem for left-orderable groups with r.e. positive cones.

## Statement

Let `A` be finitely generated and recursively presented.
1. **Order seeds are computable orders.** Suppose `A` carries an absolute order seed. That is a left order `≺` for
   which the cut at `1` satisfies the hypotheses (D) and (M) of `order-seeds-are-rigid-relative-seeds` with
   `C = 1`, for example a dense order with finitely generated positive cone. Then `≺` is computable, and `A` has
   decidable word problem.
2. **Computable orders pass to subgroups that act freely somewhere.** Suppose `A` has decidable word
   problem and carries a relative order seed for `(A, C)`, and `Γ ≤ A` is finitely generated. If some orbit point `q = g·p` has `Stab_Γ(q) = 1`, then
   `h ↦ cmp(h·q, q)` is a computable left order on `Γ`, in `Γ`'s own generators.
3. **The absolute route misses some decidable left-orderable groups.** Darbinyan's Corollary 2 group, and
   Harrison-Trainor's group, embed in no group with an absolute order seed. More generally they embed in no
   recursively presented group with a computable left order, since such an order restricts.
   - So absolute order seeds cannot seed every decidable left-orderable input.
   - A fortiori, finitely presented groups with finitely generated positive cones cannot.

*Proof.*
1. `A` is recursively presented, and the seed is an isolated point with trivial stabilizer. By
   `seeded-recursively-presented-groups-have-solvable-word-problem`, `A` has decidable word problem and the forced
   point `y(g) = cmp(g, 1)` is computable, and that point is the order. (Directly, for a finitely generated positive
   cone: positivity and negativity are both c.e. from positive words, and equality is decidable.)
2. The relative seed point `y_p(g) = cmp(g·p, p)` is computable from `WP(A)`, by statement 3 of the gluing theorem
   (`relative-seeds-glue-graphs-of-groups-into-class-c`).
   - Then `cmp(h·q, q) = cmp(g^{-1}h g·p, p) = y_p(g^{-1} h g)` is computable for words `h` in `Γ`.
   - Freeness at `q` makes `h ↦ h·q` injective. The pulled-back relation is a left order, because `A` acts by order
     automorphisms.
3. By 1 and 2 (with `q = p` and `C = 1`), an embedding into such an `A` would give the embedded group a computable
   left order. Darbinyan's Corollary 2 group and Harrison-Trainor's group have none. `∎`

## What this means for question (O) and for CAP

- **(O) needs isolated orders on hard groups.** A finitely generated positive cone makes its order isolated in the
  space of left orders (standard; recalled). So (O) asks for a finitely presented group with a dense isolated left
  order whose word problem is hard.
  - The recorded finitely presented examples have easy word problems: braid groups (Dubrovina–Dubrovin orders) and
    torus-knot groups (Navas). Both recalled.
  - We know of no finitely presented group with an isolated order and a word problem outside EXP. (O) stays
    **open**.
- **Relative seeds must be stabilizer-rich.** By 2, a group without a computable left order can sit inside a
  relatively order-seeded `A` only if it fixes a point of every orbit it meets there. So a CAP counterexample or a
  (SEED) construction through order seeds must use actions with large point stabilizers, where membership, not
  order, carries the complexity.
- **Orderability alone certifies nothing.** Darbinyan's Theorem 2 gives a bi-orderable recursively presented group
  with undecidable word problem, and seeds always force decidability. So an order helps only when it is seeded, and
  then it is computable.

## Lesson for general BH

An order seed is a computable order. So the computability theory of orders (Darbinyan, Harrison-Trainor,
Bludov–Glass) bounds what order seeds reach.
- **What they cannot reach.** Some finitely presented decidable left-orderable groups embed in no group with an
  absolute order seed. Absolute order seeds are therefore not a universal (SEED) mechanism.
- **What remains.** Relative order seeds survive only through large point stabilizers.
- **CAP.** Question (O) reduces to isolated orders on finitely presented groups with hard word problems, which is
  open.
