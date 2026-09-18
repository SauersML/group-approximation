---
rg: 2
id: three-tree-lattice-kernel-commutation-proof
kind: route
title: Kernels on different factors commute modulo their intersection, and commuting normal subgroups cannot both act nontrivially on a thick tree, so some pairwise intersection survives
target: three-tree-lattices-escape-only-via-discrete-normal-subgroups
requires: [tree-lattices-split-into-irreducible-blocks, irreducible-jnc-tree-lattices-pbh-via-bader-shalom, product-of-trees-lattices-with-faithful-factor-satisfy-pbh, product-of-two-trees-lattices-satisfy-permutational-boone-higman]
---

Notation as in the target. Write `G_k = pr_k(Γ_0)`.

**Item 1.** If `Γ` is reducible, item 1 of `tree-lattices-split-into-irreducible-blocks`
makes `Γ_0` virtually a product of a lattice on one tree (virtually free) and a
lattice on two trees, both in `B_A` (item 3 there), so `Γ ∈ B_A`. If some
`K_i = 1`, item 3 of `product-of-trees-lattices-with-faithful-factor-satisfy-pbh`
gives `Γ ∈ B_A`. So assume `Γ` irreducible and every `K_i ≠ 1`.

**Lemma A (no fixed ends).** Irreducibility makes each `Ḡ_k` non-discrete, and
Steps 0–2 of `irreducible-jnc-tree-lattices-pbh-via-bader-shalom` show that it
fixes no end of `T_k`. So `G_k` fixes no end either. `T_k` is leafless and `G_k`
has finitely many orbits, so `G_k` acts minimally (Minimality in
`tree-lattice-block-splitting-proof`).

**Lemma B (normal subgroups act minimally).** Let `M ⊴ Γ_0` with `pr_k(M) ≠ 1`.
If every element of `pr_k(M)` were elliptic, `pr_k(M)` would fix a point of the
geometric tree or a unique end. A unique end is `G_k`-invariant, which Lemma A
excludes. A nonempty fixed set is a `G_k`-invariant convex set, unbounded because
`G_k` has no bounded orbit, so its vertices span a `G_k`-invariant subtree, which is
`T_k` by minimality. That contradicts `pr_k(M) ≠ 1`. So `pr_k(M)` contains a
hyperbolic element, and the same argument shows its minimal subtree, which is
`G_k`-invariant, is `T_k`.

**Lemma C (commuting normal subgroups).** Let `A, B ⊴ Γ_0` with `[A, B] = 1`.
Then `pr_k(A) = 1` or `pr_k(B) = 1` for each `k`. Otherwise take `a ∈ pr_k(A)`
hyperbolic (Lemma B). Every element of `pr_k(B)` commutes with `a`, so it
preserves `Axis(a)`, and a hyperbolic `b ∈ pr_k(B)` then has `Axis(b) = Axis(a)`.
For `g ∈ G_k`, `g b g^(-1) ∈ pr_k(B)` is hyperbolic with axis `g · Axis(a)`, which
must again equal `Axis(a)`. So `G_k` preserves a line, and by minimality `T_k` is
a line, contradicting the hypothesis of more than two ends.

**Item 2.** Suppose every `N_ij = 1`. For `i ≠ j`, `[K_i, K_j] ⊆ K_i ∩ K_j = 1`,
because both are normal. By Lemma C at the factor `1`, `pr_1(K_2) = 1` or
`pr_1(K_3) = 1`. In the first case `K_2 ⊆ K_1`, so `K_2 = N_12 = 1`; in the second,
`K_3 = N_13 = 1`. Both contradict item 1. So some `N_ij ≠ 1`, with `k` the third
index.
- `N_ij` acts trivially on `T_i` and `T_j`, so its stabilizer of a vertex of `T_k`
  fixes a vertex of `X` and is finite. It is faithful on `T_k` because `Γ` is
  faithful on `X`, and it acts minimally by Lemma B.
- If `N_ij` were finitely generated, then with generators `s_1, ..., s_m` and a
  vertex `x`, the subtree `Y` spanned by `x, s_1 x, ..., s_m x` has connected
  union `N_ij Y`, which is invariant, so it is `T_k` and the action is cocompact.
  Step 2 of `tree-lattice-block-splitting-proof` (with `I^c = {k}` and the
  kernel replaced by the cocompact, finitely generated discrete normal subgroup
  `pr_k(N_ij)` of `G_k`) then makes `G_k` discrete, contradicting irreducibility.
  The same step, with cocompactness alone, excludes a cocompact action, since a
  cocompact action with finite stabilizers on a locally finite tree is by a
  finitely generated (virtually free) group.

**Item 3.** `pr_k(N_ij)` has finite vertex stabilizers, so it is discrete. It is
normal in `G_k`, hence in `Ḡ_k`, since the normalizer of a discrete subgroup is
closed. For `d` in it, `g ↦ g d g^(-1)` is continuous from `Ḡ_k` to a discrete
set, so the centralizer of `d` is open and `d ∈ QZ(Ḡ_k)`. The subgroup is
nontrivial and not cocompact (item 2), so `Ḡ_k` is not just-non-compact.

**Criterion.** If no `Ḡ_k` has a nontrivial discrete normal subgroup, items 2 and
3 are impossible, so `Γ ∈ B_A`. By item 1 this happens through a faithful factor
or through reducibility.

**n ≥ 4 remark.** For `(n - 2)`-subsets `J ≠ J'` with `|J ∪ J'| = n - 1`, if all
kernels on `(n - 1)`-subsets vanish then `K_J` and `K_(J')` commute. Lemma C at a
factor outside `J ∪ J'`, on which both act faithfully, shows one of them is
trivial. This is recorded only as a remark.
