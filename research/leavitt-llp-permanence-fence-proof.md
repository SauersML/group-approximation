---
rg: 2
id: leavitt-llp-permanence-fence-proof
kind: route
title: Apply finite generation, property FA, quotient rigidity, and the Thompson disjoint-cylinder embeddings
target: leavitt-llp-permanence-fence
requires:
  - universal-leavitt-el4-nonsofic
  - leavitt-gl-equals-el-and-perfect-unit-group
  - leavitt-unit-group-has-no-finite-normal-subgroup
  - leavitt-cylinder-swaps-generate-thompson-in-el
---

Put `R=L_(F_2)(1,2)` and `G=R^x`.  The rank equivalences in
`leavitt-gl-equals-el-and-perfect-unit-group` identify `G` with the
property-(T) elementary groups in `universal-leavitt-el4-nonsofic`; in
particular `G` is finitely generated and has property `(T)`.  The claim
`leavitt-unit-group-has-no-finite-normal-subgroup` proves the stronger fact
that every homomorphism from `G` to a finite group is trivial.

## The three positive permanence constructions collapse

**Directed unions.**  Suppose `G` is the directed union of subgroups `G_i`.
Choose a finite generating set `S` of `G`.  Directedness supplies one `G_j`
containing the finitely many members of `S`, hence `G_j=G`.  Therefore
Fournier-Facio--Willett Corollary 3.19 cannot prove LLP of `G` from proper
LLP subgroups.

**Amenable extensions.**  Suppose

```text
1 -> K -> G -> A -> 1
```

has amenable quotient `A`.  Property `(T)` passes to quotients, and an
amenable discrete property-(T) group is finite.  The no-finite-quotient
theorem makes `A=1`, so `K=G`.  Their Theorem 3.39 therefore asks for LLP of
`C^*(G)` as its own hypothesis in every amenable-extension application.

**Finite-edge graphs of groups.**  Property `(T)` implies Serre property
`FA`: every action on a tree fixes a vertex.  The Bass--Serre action of the
fundamental group of a nontrivial reduced graph of groups has no global fixed
vertex.  Consequently every reduced finite-edge graph-of-groups decomposition
of `G` is the one-vertex decomposition, and Proposition 3.26 again has `G`
itself as a vertex hypothesis.  The finite-dimensional amalgam theorem behind
that proposition therefore supplies no Leavitt construction either.

These arguments do not claim that arbitrary C-star inductive systems or
Morita equivalences are impossible.  They show exactly that the group
permanence results currently available in Section 3 of the cited source are
circular at this candidate.

## The F2-times-F2 lower bound

The formalized faithful map
`BinaryLeavitt.vEmbedding` and
`leavitt-cylinder-swaps-generate-thompson-in-el` embed Thompson's group `V`
in `G`.  Thompson's `V` contains a nonabelian free group `F_2`.  Prefix every
table of this free subgroup by `0`, respectively by `1`, and extend it by the
identity off that cylinder.  These give two faithful copies

```text
F_2^(0), F_2^(1) <= V
```

with disjoint supports.  They commute and have trivial intersection, hence
their product is an embedded `F_2 x F_2 <= V <= G`.

Fournier-Facio--Willett Corollary 3.17 proves that LLP of full group C-star
algebras passes to subgroups (equivalently, use the canonical ucp
expectation/retraction `C^*(G) -> C^*(H)`).  Applying it twice gives

```text
LLP(C^*(G))  ==>  LLP(C^*(V))  ==>  LLP(C^*(F_2 x F_2)).
```

Their Question 1.6 states that LLP (and LP) for `F_2 x F_2` is open.  This
proves `(LLPF)` and the advertised hardness fence.
