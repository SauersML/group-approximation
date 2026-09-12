---
rg: 2
id: function-field-borel-groups-are-fp-for-three-places-citation
kind: route
title: Import Bux's finiteness theorem for soluble S-arithmetic Borel groups over global function fields
target: function-field-borel-groups-are-fp-for-three-places
requires: []
artifacts:
  - research/artifacts/bh-metabelian-products-2026-09-12.md
---

Citation import with a routine deduction.

**Theorem A (Bux, arXiv:math/0212365, Geom. Topol. 8 (2004)).** Quoted in the
claim, from the arXiv TeX source on MSI. Type `F_2` means finitely presented. So
for `|S| >= 3` and every `n >= 2`, the group `B^SL_n(O_S)` of upper triangular
determinant-one matrices over `O_S` is finitely presented, since `SL_n` is a
Chevalley group.

**GL_n.** Let `B_n(O_S)` be the group of all invertible upper triangular
matrices over `O_S`.
- *Splitting.* The determinant is a surjective homomorphism
  `B_n(O_S) -> O_S^x` with kernel `B^SL_n(O_S)`, split by
  `λ -> diag(λ, 1, ..., 1)`. So `B_n(O_S) = B^SL_n(O_S) x| O_S^x`.
- *The quotient.* `O_S^x` is a finitely generated abelian group by the S-unit
  theorem, so it is finitely presented.
- *Extensions.* An extension of a finitely presented group by a finitely
  presented group is finitely presented.

So `B_n(O_S)` is finitely presented for `n >= 2` and `|S| >= 3`. For `n = 1` it
is `O_S^x`, which is finitely presented for every nonempty `S`.

**Prior use.** Kochloukova--Sidki, arXiv:1710.04745, invoke the same theorem for
the upper triangular groups `U(m, A)` over `A = F_p[x^±1, 1/f_1, ..., 1/f_(n-1)]`
(TeX source read on MSI).

Not reproved; no Lean counterpart.
