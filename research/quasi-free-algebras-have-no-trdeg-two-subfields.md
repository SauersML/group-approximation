---
rg: 2
id: quasi-free-algebras-have-no-trdeg-two-subfields
kind: claim
title: A k-algebra of Hochschild dimension at most one, and every matrix ring over it, has no commutative subfield of transcendence degree two
distinct_from:
  leavitt-tensor-global-dimension-bound: that is the upper bound gl.dim(B ⊗ L^(⊗d)) <= gl.dim B + d for the Leavitt algebra; this pairs the same kind of upper bound with a Koszul lower bound coming from a subfield, and applies to every quasi-free algebra.
  matrices-over-free-fields-have-no-trdeg-two-subfields: that is the free-skew-field instance; this is the general homological statement it follows from.
---

**ESTABLISHED** by `quasi-free-subfield-bound-via-koszul-ext` (unreviewed).

Let `k` be a field and `A` a `k`-algebra with `pd_(A^e) A <= 1`, where `A^e = A ⊗_k A^op`. Such an `A` is
quasi-free in the sense of Cuntz--Quillen.

1. **Upper bound.** For every semisimple `k`-algebra `U`, `l.gl.dim(A ⊗_k U) <= 1`. In particular this holds
   when `U` is a commutative field, and when `U = A^op` for a division ring `A`.
2. **Lower bound.** Let `A'` be any `k`-algebra with a subfield `F ⊆ A'` such that `k · 1 ⊆ F` and
   `F ≅ K = k(y_1, ..., y_n)`. Then `l.gl.dim(A' ⊗_k K) >= n`.
3. **Consequence.** For every `r >= 1`, every commutative subfield `F ⊆ M_r(A)` with `k · 1 ⊆ F` has
   `trdeg_k F <= 1`.

In particular, no commuting pair `a, b ∈ M_r(A)` has every nonzero `p(a, b)`, with `p ∈ k[x, y] ∖ 0`, invertible,
unless `a` and `b` are algebraically dependent.

Instances:
- the free skew field (`matrices-over-free-fields-have-no-trdeg-two-subfields`);
- the Leavitt algebra (`leavitt-algebras-have-no-trdeg-two-subfields`).
