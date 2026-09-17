---
rg: 2
id: tits-independence-vertex-groups-are-branch-type-proof
kind: route
title: Peel a ball fixator one boundary edge at a time with (P), and read the vertex stabilizer as a branch group
target: tits-independence-vertex-groups-are-branch-type
requires: [micro-supported-tree-actions-self-embed-rigid-stabilizers]
---

The notation is that of the target. Automorphisms of `T` are identified with
their actions, since the action is faithful.

**0. Preliminaries.**

- For `f = (x, y)`, an element of `R(Y_f)` fixes `x` and every neighbour of `x`
  other than `y`, so it fixes `y`. It preserves `Y_f` and fixes `f`.
- Rigid stabilizers of pairwise disjoint half-trees commute. Finitely many of
  them generate their direct product, because a product `g_1 ⋯ g_m` acts on the
  `i`-th half-tree as `g_i` (as in (F1) of
  `micro-supported-tree-actions-self-embed-rigid-stabilizers-proof`).
- For distinct `f, f' ∈ E_r(v)`, the half-trees `Y_f` and `Y_{f'}` are disjoint.
  Every vertex at distance `≥ r` from `v` lies in exactly one of them, and
  `Y_f ∩ B_r(v) = {y}`.

**1. Item 1.**

*The product is contained in the fixator.* An element of `R(Y_f)`, for
`f ∈ E_r(v)`, fixes `T ∖ Y_f`, which contains `B_r(v) ∖ {y}`, and it fixes `y`. So
it fixes `B_r(v)`. By 0, the product over `E_r(v)` is direct.

*The fixator is contained in the product.* Let `g ∈ Fix(B_r(v))`, and enumerate
`E_r(v) = {f_1, ..., f_m}`. This is finite by local finiteness. Put `h_0 = g`. By
induction on `j`, build `g_j ∈ R(Y_{f_j})` and `h_j` such that

- `h_{j−1} = g_j h_j`;
- `h_j` fixes `B_r(v) ∪ Y_{f_1} ∪ ... ∪ Y_{f_j}` pointwise.

*Step.*

- `h_{j−1}` fixes `B_r(v)`, hence the edge `f_j`. By (P),
  `h_{j−1} = g_j h_j` with `g_j ∈ R(Y_{f_j})` and `h_j ∈ R(Y_{f̄_j})`. So `h_j`
  fixes `Y_{f_j}`.
- `g_j` fixes `B_r(v)` by the first half of this step, and it fixes
  `T ∖ Y_{f_j} ⊇ Y_{f_i}` for `i < j`.
- `h_{j−1}` fixes `B_r(v) ∪ Y_{f_1} ∪ ... ∪ Y_{f_{j−1}}` by induction.
- So `h_j = g_j^{-1} h_{j−1}` fixes `B_r(v) ∪ Y_{f_1} ∪ ... ∪ Y_{f_j}`.

After `m` steps, `h_m` fixes `B_r(v) ∪ ⋃_i Y_{f_i} = T`, so `h_m = 1`. Hence
`g = g_1 g_2 ⋯ g_m`, which lies in the product.

*Index and normality.* `Γ_v` preserves the finite set `B_r(v)`, so `Fix(B_r(v))`
is the kernel of `Γ_v → Sym(B_r(v))`. It is normal of finite index.

**2. Item 2.**

- Faithfulness on `(T, v)` is faithfulness on `T`.
- For `y ∈ S_r(v)` with last edge `f`, the descendants of `y` in the rooted tree
  form exactly `Y_f`. So the rigid stabilizer `rist_{Γ_v}(y)`, of the elements
  fixing every non-descendant, is `R(Y_f)`. It already lies in `Γ_v`.
- By 1, `∏_{y ∈ S_r(v)} rist(y) = Fix(B_r(v))`, of finite index.
- `⋂_r Fix(B_r(v))` fixes `T`, so it is trivial. A decreasing chain of finite-index
  normal subgroups with trivial intersection makes `Γ_v` residually finite.
- A subgroup with property FA fixes a vertex of `T` (Serre), so it lies in some
  `Γ_v`, and it is residually finite.

**3. Item 3.** Induction on `r`.

- *Base.* `Γ_v` is transitive on `S_1(v)`, because the local action is transitive.
- *Step.* Suppose `Γ_v` is transitive on `S_r(v)`, and let `u, u' ∈ S_{r+1}(v)`
  with parents `p, p'`. Pick `γ ∈ Γ_v` with `γp = p'`. Then `γu` and `u'` are
  children of `p'`.
- Let `f = (q, p')` be the last edge of `[v, p']`. `Γ_{p'}` acts 2-transitively on
  the neighbours of `p'`, so `Γ_f = Γ_{p'} ∩ Γ_q` is transitive on the children of
  `p'`.
- By (P), `Γ_f = R(Y_f) R(Y_{f̄})`, and `R(Y_{f̄})` fixes `Y_f`, which contains
  every child of `p'`. So `R(Y_f)` alone is transitive on the children of `p'`.
- By 1, `R(Y_f) ≤ Fix(B_r(v)) ≤ Γ_v`. So some `δ ∈ R(Y_f)` has `δγu = u'`.

Transitivity on every sphere makes `(T, v)` spherically homogeneous, and with 2 the
definition of a branch group in Bartholdi--Grigorchuk--Šunić, "Branch groups"
(Handbook of Algebra 3, 2003), §1, is satisfied.

**4. Item 4.**

- If some `Γ_f ≠ 1`, then by (P) one of `R(Y_f)`, `R(Y_{f̄})` is nontrivial. So
  hypothesis (N) of `micro-supported-tree-actions-self-embed-rigid-stabilizers`
  holds, and (M) is assumed.
- Its items 1 and 2 give `R(Y) ≠ 1`, `R(Y)` infinite and `⊕_N R(Y) ↪ R(Y)` for
  every half-tree.

**5. Item 5.**

- **Finite quotient.** A finitely generated group acting minimally on a tree,
  not fixing a vertex, has finite quotient graph (Bass, "Covering theory for
  graphs of groups", J. Pure Appl. Algebra 89, 1993, §7).
- **Graph of groups.** By Bass--Serre theory, `Γ` is the fundamental group of a
  finite graph of groups whose vertex groups are the `Γ_v` and whose edge groups
  are the `Γ_f`.
- **Transfer.** If the fundamental group of a finite graph of groups and all its
  edge groups are finitely presented, so are its vertex groups (see
  Guirardel--Levitt, "JSJ decompositions of groups", Astérisque 395, 2017, §1).
  Conjugates of finitely presented groups are finitely presented.
- **Hypothesis.** This is why edge stabilizers are assumed finitely presented
  rather than only finitely generated. The finitely generated version is not
  claimed here.

**6. Item 6.** Combine items 2, 3, 4 and 5. ∎

**Scope.**

- Local finiteness is used twice: in 1, to terminate the peeling, and in 2, for
  finite index. With infinite valence the peeling gives only the restricted
  product `⊕_{f ∈ E_r(v)} R(Y_f) ≤ Fix(B_r(v))`, and equality can fail.
- Faithfulness is used in 1, at `h_m = 1`.
- Nothing is claimed about the converse. A finitely presented branch group need
  not be a vertex group of a (P)-amalgam.
