---
rg: 2
id: elek-amenable-algebras-almost-have-fd-representations
kind: claim
title: Elek — an amenable algebra almost has finite dimensional representations, the rank radical is an ideal, and a simple such algebra is stably finite
---

Literature import (G. Elek). Let `k` be a field and `A` a unital `k`-algebra.

**Amenability** (Elek, arXiv:math/0311376): `A` is amenable if for any finite dimensional linear subspace
`1 ∈ B ⊂ A` and `ε > 0` there exists a non-trivial finite dimensional linear subspace `Q ⊂ A` such that
`(dim_k BQ − dim_k Q)/dim_k Q < ε`.

**Almost finite dimensional representability** (same paper): `A` almost has finite dimensional
representations if for any finite dimensional `1 ∈ L ⊂ A` and `ε > 0` there are a finite dimensional `V`,
a subspace `V_ε ⊂ V` and a linear `ψ_{L,ε} : L → End(V)` with `ψ(1) = I`, with
`ψ(a)ψ(b)(v) = ψ(ab)(v)` whenever `a, b, ab ∈ L` and `v ∈ V_ε`, and `(dim V − dim V_ε)/dim V < ε`.

Imported statements:
- **(E1)** If `A` is amenable then `A` almost has finite dimensional representations. The proof is the
  compression `ψ_n(a)v = P_n(av)` onto a nearly invariant finite dimensional subspace.
- **(E2)** The rank radical `RR(A)` is an ideal.
- **(E3)** If `A` is simple and almost has finite dimensional representations, then `A` is stably finite.

From the companion paper, arXiv:math/0203261:
- **(E4)** Any affine algebra of subexponential growth is amenable.
- **(E5)** For affine algebras **without zero divisors**, amenable ⟺ not paradoxical ⟺ there is a finitely
  additive invariant dimension-measure. The zero-divisor hypothesis is essential and must not be dropped:
  the crossed products used in this program have idempotents.
