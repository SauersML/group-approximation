---
rg: 2
id: acyclic-quotientless-extension-completion-proof
kind: route
title: Conjugation is inner on every admissible finite image, and the centralizer is a split central extension of Q
target: acyclic-quotientless-extension-completion-is-kernel-completion
requires: []
artifacts:
  - research/artifacts/hyperbolic-no-finite-quotient-leavitt-cover-2026-09-12.md
---

Pure group theory. The full proof is in §1 of the artifact.

1. **Inner action.** Let `K` be admissible. Conjugation gives
   `G -> Aut(N/K)`. Composing with `Aut -> Out` kills `N`, so it factors
   through `Q`. Its image is finite, hence trivial. Put
   `C = C_(G/K)(N/K)` and `Z = Z(N/K)`. Then `C·(N/K) = G/K` and
   `C ∩ N/K = Z`.
2. **Splitting.** `C/Z ≅ Q`, and `Z` is central in `C`. With trivial
   coefficients, `H^2(Q; Z) = Hom(H_2 Q, Z) ⊕ Ext(H_1 Q, Z) = 0`, so
   `C = S x Z` with `S ≅ Q`.
   - Since `Q` is perfect, `S = [C,C]`. That is characteristic in the normal
     subgroup `C`, so `S` is normal in `G/K`.
   - `S ∩ N/K ⊆ S ∩ Z = 1`, and `S·(N/K) ⊇ S·Z·(N/K) = C·(N/K) = G/K`.

   This gives item 1.
3. **Finite quotients.** Let `φ : G ->> F` be finite. Then `F/φ(N)` is a
   finite quotient of `Q`, so `φ(N) = F` and `F ≅ N/K` with
   `K = N ∩ ker φ` admissible. Conversely, item 1 projects `G/K` onto `N/K`.
   Since `N` is finitely generated, it has finitely many subgroups of each
   index. So a finite-index normal `M ◁ N` has finitely many `G`-conjugates,
   and their intersection is admissible. This gives item 2.
4. **Completions.** Every finite quotient `G/L` receives `N` onto it, and the
   kernels `N ∩ L` are cofinal among finite-index normal subgroups of `N`.
   So `N^ -> G^` has dense image and is injective, and it is onto by
   compactness. Intersecting over `L` gives `R_f(G) ∩ N = R_f(N)`. Item 4 is
   item 2 read in both directions.
5. **Circularity.** Step 1 used only that `Q` has no finite quotients. If `G`
   has none, the finite quotient `G ->> Inn(N/K)` is trivial for every
   admissible `K`, so `N/K` is abelian. Every finite quotient of `N` factors
   through some such `N/K`, so it is abelian.
   - If `N^ab` is finite, `[N,N]` has finite index and is finitely generated.
   - A finite-index normal `M ◁ [N,N]` has finitely many `N`-conjugates, whose
     intersection `L` is normal of finite index in `N`.
   - `N/L` is abelian, so `[N,N] ⊆ L ⊆ M`.
6. **Sharpness.** Let `Q` be perfect with a surjection `H_2(Q) ->> A`, `A`
   finite. Quotient the universal central extension by the kernel of that
   surjection. The result `G` is perfect with central kernel `A`.
   - Any finite image `F` of `G` equals the image of `A`, hence is abelian.
   - Being a quotient of a perfect group, `F` is perfect, so `F = 1`.
