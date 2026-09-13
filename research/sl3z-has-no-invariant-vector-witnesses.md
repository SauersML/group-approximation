---
rg: 2
id: sl3z-has-no-invariant-vector-witnesses
kind: claim
title: No finite family of nonamenable subgroups of SL_3(Z) has fixed vectors in every finite-dimensional representation
artifacts:
  - research/artifacts/sl3z-invariant-vector-witnesses-2026-09-12.md
---

ESTABLISHED (unreviewed).  For every finite family `H_1, ..., H_k` of
nonamenable subgroups of `SL_3(Z)` there are irreducible unitary
representations `pi` of `SL_3(Z)` with finite image and arbitrarily large
dimension such that `pi` has no nonzero `H_j`-fixed vector for any `j`.

This is the mechanism of Magee--de la Salle (arXiv:2312.03220v2, Theorem 1.1
and Corollary 1.3): for `SL_4(Z)` the block `SL_2(Z)` alone has a fixed
vector in every finite-dimensional representation, which together with Kesten's
criterion excludes strong convergence to the regular representation.  The claim
says that no version of this argument with finitely many witness subgroups can
prove `SL_3(Z)` not purely matricial field.  It extends Deligne's example (MdlS
Example 2.2, block `SL_2` only) to every nonamenable subgroup, including the
principal `SL_2 = Sym^2(SL_2(Z))`, which does have fixed vectors in Deligne's
representations (`deligne-sl3-representations-have-principal-sl2-invariants`).

It does not decide whether `SL_3(Z)` is purely matricial field
(`sl3z-purely-matricial-field`).
