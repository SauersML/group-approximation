---
rg: 2
id: crossed-product-el-kazhdan-iff-finite-field-and-subshift
kind: claim
title: For a zero-dimensional system (X,T) and a field k, EL_n(LC(X,k) ⋊ Z) with n ≥ 3 is Kazhdan iff it is finitely generated iff k is finite and X is a subshift
distinct_from:
  odometer-crossed-product-elementary-groups-not-kazhdan: that is one non-expansive example, the dyadic odometer over a finite field; this is the equivalence for every zero-dimensional system and every field.
---

**ESTABLISHED (unreviewed)** by `crossed-product-el-kazhdan-iff-finite-field-and-subshift-proof`.

**Statement.** Let `X` be a nonempty compact metrizable zero-dimensional space, `T` a homeomorphism of `X`, `k` a field, `R = LC(X,k) ⋊_T Z` (finite sums `Σ f_j u^j`, `u f u^(-1) = f∘T^(-1)`), and `n ≥ 3`. The following are equivalent:
1. `R` is finitely generated as a ring.
2. `EL_n(R)` is finitely generated.
3. `EL_n(R)` has property (T).
4. `k` is finite and `(X,T)` is topologically conjugate to a subshift over a finite alphabet.

**Use for the note** (`simple_kazhdan_sofic_group.tex`, lane sk-hypotheses-sharp): among zero-dimensional systems and coefficient fields, the hypotheses "subshift over a finite alphabet" and "`F_2`" are the ones that give finite generation and property (T). For an infinite minimal system that is not expansive (e.g. an odometer), or for an infinite field, `EL_n(R)/Z` is still simple (`steinberg-elementary-groups-are-simple-mod-centre`), but it is not finitely generated and has no property (T).

The infinite-field half was derived independently in `research/artifacts/sk-coefficients-proposal-2026-09-13.md` §5.
