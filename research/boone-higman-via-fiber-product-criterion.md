---
rg: 2
id: boone-higman-via-fiber-product-criterion
kind: route
title: Act with the fiber product on the kernel and read off a type (A) action
target: boone-higman-conjecture
requires: [universal-fiber-product-data-for-word-problem-groups, fiber-product-conjugation-action-lemma, one-two-three-fibre-product-theorem, type-a-action-gives-boone-higman-for-subgroups]
artifacts:
  - research/artifacts/boone-higman-fiber-product-and-shift-compiler-2026-08-24.md
---

Let `G` be finitely generated with solvable word problem.  By
`universal-fiber-product-data-for-word-problem-groups` choose `T` and
`N <| T` with `G <= T`, `T` finitely presented, `N` finitely generated,
`Q = T/N` of type `F_3`, `C_T(N) = 1`, and finitely many `T`-conjugacy
classes in `N`.  Put

    Gamma  =  T x_Q T .

By `one-two-three-fibre-product-theorem` -- `N` finitely generated, `T`
finitely presented, `Q` of type `F_3` -- `Gamma` is finitely presented.

By `fiber-product-conjugation-action-lemma`, `Gamma` acts on the set `N` by
`(a,b) . x = a x b^{-1}`, and that action is transitive with point
stabilizer `Delta T`, has ordered-pair orbits in bijection with the
`T`-conjugacy classes of `N`, and has kernel `Delta C_T(N)`.

Check the four clauses of type (A):

* **faithful** -- because `C_T(N) = 1`;
* **`Gamma` finitely presented** -- the 1-2-3 theorem, above;
* **point stabilizers finitely generated** -- every one is conjugate to
  `Delta T = T`, which is finitely presented;
* **finitely many orbits of two-element subsets** -- orbits of two-element
  subsets are quotients of orbits of ordered pairs of distinct elements, and
  those are the `T`-conjugacy classes of `N`, finite in number by hypothesis.

So `type-a-action-gives-boone-higman-for-subgroups` applies to
`Gamma`.  `Delta T <= Gamma` and `G <= T`, so `G` is a subgroup of `Gamma`
and therefore embeds in a finitely presented simple group.  `∎`

## Why every prerequisite is genuinely used

The data claim is the only open input.  The lemma supplies three of the four
type (A) clauses by computation and is used nowhere else.  The 1-2-3 theorem
supplies the fourth and is the only reason clause `F_3` appears in the data
claim at all -- delete it and the fibre product need not be finitely
presented.  The imported corollary supplies the conclusion, including
simplicity, which this route never has to construct.

## Why this is a reduction and not a restatement

The prerequisite can fail, does not mention a simple group, and does not
mention finite presentability of any quotient.  Recovering the target from it
is a genuine step: the simple group is built by an external construction
(the twisted Brin--Thompson group of the action) that the prerequisite never
refers to.  Concretely, the prerequisite is a statement about a group and one
of its normal subgroups; the target is a statement about the existence of a
simple group with a finite presentation.  Nothing in the graph derives the
prerequisite from the target.

## How this differs from the existing bi-index route

`boone-higman-via-finite-bi-index-envelope` reaches the same imported
criterion through the **coset** action of the Chatterji--Kassabov envelope on
`Gamma/S`, where the open input is finiteness of a double coset set and
faithfulness comes from the normal-generation near-solution.  This route
reaches it through a **two-sided translation** action on a normal subgroup,
where the open input is existence of the group and faithfulness is a
centralizer condition.  The two open inputs are about different objects and
neither is known to imply the other.  Kept separately for that reason; if a
later session shows one implies the other, merge and keep the factored one.

The honest comparison with the bi-index route: that route starts from groups
that already exist (the envelope is constructed by two theorems in print) and
asks one finiteness question about them, so it can be attacked by computing.
This route asks for a group to exist at all, which is harder to start on, but
its hypothesis list is short, checkable, and mentions no simple group -- the
whole point being that simplicity is never a hypothesis anywhere in the
chain.
