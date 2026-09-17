---
rg: 2
id: fpbs-lackenby-cocycle-support-toolkit
kind: claim
title: Mod-p cocycles lift to elementary abelian covers with controlled support and their span has a sub-span of definitely smaller support
distinct_from:
  fpbs-lackenby-rapid-descent-p-large: that is the end theorem of the same paper; this imports the two intermediate support theorems and the Schreier inequality, which are needed separately because the theorem does not apply to families that are not abelian p-series.
artifacts:
  - research/artifacts/fpbs/docs/kazhdan-mod-p-growth-2026-09-17.md
---

Three results from Lackenby, *Detecting large groups*.

1. **Theorem 5.1.** Let `K` be a finite connected 2-complex with `r` 2-cells.
   Let `U` be a set of `u` cellular 1-cocycles representing linearly
   independent classes in `H^1(K;F_p)`. Let `q: K~ -> K` be a finite regular
   cover with elementary abelian deck group of rank `n`. Then `K~` carries at
   least `(n-u)u - r` cocycles that represent linearly independent classes and
   are supported in `q^(-1)(supp U)`.
2. **Theorem 6.1.** Let `V` be a subspace of `F_p^E` of dimension `v`, and
   `w < v`. Then `V` contains a `w`-dimensional `W` with
   `|supp W| <= (p^(w+1)-p)/(p^(w+1)-1) |supp V|`.
3. **Lemma 3.3.** If `K` is normal of `p`-power index in a finitely generated
   `G`, then `d_p(K) <= (d_p(G)-1)[G:K] + 1`.

This is a literature import.
