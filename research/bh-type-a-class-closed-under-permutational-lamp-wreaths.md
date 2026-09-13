---
rg: 2
id: bh-type-a-class-closed-under-permutational-lamp-wreaths
kind: claim
title: Finite lamps over a type (A) actor give a type (A) actor, so permutational lamp wreaths lie in the permutational Boone--Higman class
distinct_from:
  type-a-actions-closed-under-products-and-finite-wreaths: that builds actors from products and from wreaths with a FINITE top group Sym_k acting imprimitively; this puts a finite LAMP group at every point of an infinite actor set, a permutational wreath product with infinite base.
  boone-higman-type-a-class-closed-under-finite-extensions: that is closure of the class B_A under finite direct products and finite-index overgroups; this is closure under restricted permutational wreath products B wr_S Gamma with finite B over a type (A) action of Gamma on S.
artifacts:
  - research/artifacts/solve-bh-apapa-2026-09-13.md
---

**ESTABLISHED** by `bh-type-a-lamp-wreath-closure-proof`. No priority is claimed:
the finite-presentation half is Cornulier's theorem, and the rest is a check of
the four clauses.

Use the definition of type (A) in `type-a-action-gives-boone-higman-for-subgroups`
(faithful, finitely presented actor, finitely generated point stabilizers,
finitely many orbits of two-element subsets).

**Statement.** Let `Gamma` act on a set `S` with `|S| >= 2`, of type (A), and let
`B` be a finite nontrivial group. Let `W = B wr_S Gamma = B^(S) x| Gamma` be the
restricted permutational wreath product, with `(gamma . f)(s) = f(gamma^-1 s)`.
Then the action

```text
(f, gamma) . (s, b) = (gamma s, f(gamma s) b)        on  S x B              (LW)
```

is of type (A). Consequently every subgroup of `W` has solvable word problem and
embeds in a finitely presented simple group, and `W` lies in the class `B_A`.

**Use for Boone--Higman.** A group `G` satisfies Boone--Higman as soon as it
embeds in `B wr_S Gamma` for some finite `B` and some type (A) action of `Gamma`.
For split extensions `G = T x| M` this is the placement "`M` inside the actor,
the module `T` inside the lamps". `kms-configuration-modules-avoid-abelian-lamp-bases`
shows that placement is impossible for the algorithmically complex groups of
Kharlampovich--Myasnikov--Sapir when `B` is abelian.
