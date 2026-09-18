---
rg: 2
id: displaced-perfect-subgroups-are-elliptic-in-tree-actions
kind: claim
title: A perfect subgroup that commutes with one of its conjugates acts by elliptic elements on every tree, and three such covering subgroups give FA
distinct_from:
  fg-perfect-wreath-c2-has-property-fa: that proves FA for the one group (A x A) ⋊ C_2 and routes through the swap; this is an elementwise ellipticity lemma inside an arbitrary ambient group, plus a Helly criterion over three subgroups, with no wreath structure and no finite-index overgroup.
  property-t-implies-property-fa: that certifies FA through Kazhdan rigidity; this uses only perfectness and commuting conjugates, which hold in Thompson-like groups that are a-T-menable.
  baumslag-gersten-base-is-elliptic-in-every-tree-action: that proves one specific subgroup elliptic by a translation-length count in a one-relator group; this is a general commuting-conjugate criterion.
---

Let `Γ` act on a tree without inversions.

**(E) Ellipticity.** Let `P <= Γ` be perfect, and suppose `g in Γ` satisfies
`[P, gPg^-1] = 1`. Then every element of `P` fixes a vertex.

**(FA) Criterion.** Suppose `Γ = <K_1, K_2, K_3>`, and for all `i, j` there is a
finitely generated subgroup `Q_ij <= Γ` containing `K_i` and `K_j` that is perfect
and commutes with one of its own conjugates (`Q_ii` included). Then `Γ` fixes a vertex. So `Γ`
has Serre's property FA.

The route `displaced-perfect-subgroups-are-elliptic-in-tree-actions-proof` proves
both from scratch. It uses only geodesics in trees, the no-backtracking concatenation principle and
the solvability of the infinite dihedral group.

**Where perfectness is used.** Only to force a group acting on a line to act
trivially on it. For `P = Z` acting on a line by translation inside `Γ = Z x Z`
(which commutes with every conjugate), (E) fails.

**Consumer.** `twisted-brin-thompson-fa-from-simplicity-by-tree-geometry` takes the `K_i` to be the
rigid stabilizers of three clopen sets whose pairwise unions are proper.
