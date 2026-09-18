---
rg: 2
id: comm-of-z-n-times-torsion-group-splits-proof
kind: route
title: FC-centres and torsion sets are preserved by isomorphisms of finite-index subgroups, so commensurations split
target: comm-of-z-n-times-torsion-group-splits
requires: []
---

Direct proof. Lane proof, not independently reviewed.

Recall that `Comm(G)` is the set of isomorphisms `φ : H_1 -> H_2` between
finite-index subgroups of `G`, modulo agreement on a finite-index subgroup. Its
product is composition on the common domain.

## Step 1: `Comm(Z^n) = GL_n(Q)`

An isomorphism `φ : L_1 -> L_2` between finite-index subgroups of `Z^n` extends
uniquely to a `Q`-linear automorphism of `L_1 ⊗ Q = Q^n`. Two commensurations
agree on a finite-index subgroup iff their extensions are equal. Conversely, each
`g ∈ GL_n(Q)` maps `Z^n ∩ g^{-1} Z^n` onto `g Z^n ∩ Z^n`, and both have finite
index. So `Comm(Z^n) ≅ GL_n(Q)`.

## Step 2: invariant subsets

Let `G = A x B` with `A = Z^n` and `B` as in the statement. Let `H` have finite index
in `G`.
- **FC-centre.** `FC(H) = H ∩ FC(G)`:
  - if `h` has `k` conjugates in `H` and `G = g_1 H ∪ ... ∪ g_r H`, then `h` has at
    most `rk` conjugates in `G`;
  - conversely, a finite `G`-class contains the `H`-class.

  In a direct product, `(a, b)` has finitely many conjugates iff `a` and `b` do. So
  `FC(G) = A x FC(B) = A x 1`, and `FC(H) = H ∩ A`.
- **Torsion.** `A` is torsion-free and every element of `B` has finite order. So the
  elements of finite order in `G` are exactly `1 x B`, and those of `H` are
  `H ∩ B`, a subgroup.

Both subsets are defined intrinsically in the group. So an isomorphism
`φ : H_1 -> H_2` maps `H_1 ∩ A` onto `H_2 ∩ A`, and `H_1 ∩ B` onto `H_2 ∩ B`.

## Step 3: splitting

- **A product subgroup.** `A_1 := H_1 ∩ A` has finite index in `A`, and
  `B_1 := H_1 ∩ B` has finite index in `B`. So `A_1 x B_1` has finite index in `G`,
  and lies in `H_1`.
- **The restriction is a product.** By Step 2,
  `φ(a, b) = (α(a), 1) · (1, β(b))`, where `α : A_1 -> H_2 ∩ A` and
  `β : B_1 -> H_2 ∩ B` are isomorphisms onto finite-index subgroups.
- **The splitting map.** Define `Φ([φ]) = ([α], [β])`. It is well defined:
  commensurations that agree on a finite-index subgroup `W` agree on `W ∩ (A_1 x B_1)`,
  whose intersections with `A` and `B` have finite index.
- **It is an isomorphism.** `Φ` is a homomorphism, since composites restrict to
  composites. It is injective: if `[α]` and `[β]` are trivial, then `φ` is the
  identity on a product of finite-index subgroups. It is surjective: `α x β` is a
  commensuration of `G` for any commensurations `α` of `A` and `β` of `B`.

So `Comm(A x B) ≅ Comm(A) x Comm(B) = GL_n(Q) x Comm(B)`. A group with a quotient that
is not finitely generated is not finitely generated, and `GL_n(Q)` is not finitely
generated (a finitely generated subgroup has entries in some `Z[1/N]`).

## Step 4: Grigorchuk-type `B`

Let `B` be infinite, finitely generated, just-infinite, and torsion (for example
Grigorchuk's group; that it is just-infinite is classical and not re-proved here).
- `FC(B)` is characteristic, hence normal.
- If `FC(B) ≠ 1`, it has finite index, since `B` is just-infinite. Then it is a
  finitely generated FC-group. The centralizers of its finitely many generators have
  finite index, so its centre has finite index, and `B` is virtually abelian.
- A finitely generated virtually abelian torsion group is finite, which is a
  contradiction.

So `FC(B) = 1`, and the statement applies.
