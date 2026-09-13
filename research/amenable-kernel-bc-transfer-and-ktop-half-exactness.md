---
rg: 2
id: amenable-kernel-bc-transfer-and-ktop-half-exactness
kind: claim
title: Baum--Connes transfers along amenable normal subgroups, separately for injectivity and surjectivity, and topological K-theory is half exact in the coefficients
distinct_from:
  bc-kun-thom-gap-labels-on-bc-subgroups-pass-trace-test: that imports Lück's trace theorem and Higson--Kasparov for subgroups; this imports the Chabert--Echterhoff extension theorem and the half-exactness of topological K-theory, which relate a group extension to crossed products by the quotient.
---

**ESTABLISHED (citation)** by `amenable-kernel-bc-transfer-and-ktop-half-exactness-citation`.

Groups are countable and discrete. BCI and BCS mean injectivity and surjectivity of the
assembly map `mu : K^top_*(G; B) -> K_*(B ⋊_r G)`.

1. **Amenable kernels.** Let `1 -> N -> Γ -> Γ/N -> 1` be an extension with `N` amenable,
   and `B` a `Γ`-algebra. The partial assembly map
   `K^top_*(Γ; B) -> K^top_*(Γ/N; B ⋊_r N)` is bijective. Hence `Γ` satisfies BCI (resp. BCS)
   for `B` iff `Γ/N` satisfies BCI (resp. BCS) for the twisted algebra `B ⋊_r N`.
2. **Semidirect products with abelian kernel.** For `Γ = N ⋊ G`, `N` abelian and `B = C`, the
   coefficient algebra is `C*_r(N) ≅ C(N^)`. Here `G` acts through its action on `N`, and
   `C*_r(Γ) = C(N^) ⋊_r G`. So reduced assembly for `Γ` is injective (resp. surjective) iff
   assembly for `G` with coefficients `C(N^)` is. Chabert--Echterhoff use exactly this form
   in their Example 4.3.
3. **Half-exactness.** For every group `G`, the functor `A ↦ K^top_*(G; A)` turns each short
   exact sequence of `G`-algebras into a natural six-term exact sequence, and assembly is
   natural in `A`.
4. **K-exactness is necessary.** Hence Baum--Connes with coefficients can hold for `G` only if
   `G` is K-exact: for every short exact sequence `0 -> I -> A -> A/I -> 0` of `G`-algebras,
   `K_*(I ⋊_r G) -> K_*(A ⋊_r G) -> K_*(A/I ⋊_r G)` is exact in the middle.

Items 1, 3 and 4 are quoted from the source. Item 2 is the split case, with the
identification Chabert--Echterhoff themselves use for `K^n ⋊ SL_n(K)`.
