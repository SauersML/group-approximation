---
rg: 2
id: algebraic-cartan-pairs-are-effective-groupoid-steinberg-algebras
kind: claim
title: Algebraic Cartan pairs over an indecomposable ring are exactly twisted Steinberg algebras of effective ample Hausdorff groupoids with their diagonals
---

Let `R` be an indecomposable commutative ring. Following Armstrong–de Castro–Clark–Courtney–Lin–McCormick–Ramagge–
Sims–Steinberg, a pair `(A,B)` of an `R`-algebra `A` and a commutative subalgebra `B` is an **algebraic Cartan pair**
when:
- the idempotents of `B` are local units for `A`, and span `B`;
- `A` is spanned by the inverse-semigroup normaliser `N(B)`;
- a faithful conditional expectation `A → B` exists;
- `B` is maximal commutative.

The torsion condition of their definition holds automatically when `R` is a field.

Then:
1. Every algebraic Cartan pair is an algebraic quasi-Cartan pair (`lem:C=>Q`).
2. For an algebraic quasi-Cartan pair, the ultrafilter construction gives a discrete `R`-twist `Σ` over an ample groupoid
   `G`, which is Hausdorff (`prop:Hausdorff`). It also gives an isomorphism `A ≅ A_R(G;Σ)` taking `B` onto the
   diagonal `A_R(G^(0); q^{-1}(G^(0))) ≅ A_R(G^(0))` (`thm:main`).
3. A quasi-Cartan pair is a Cartan pair if and only if `G` is effective (`prop:effective`(a)).
4. Conversely, a discrete `R`-twist over an effective ample Hausdorff groupoid `G` gives an algebraic Cartan pair
   `(A_R(G;Σ), A_R(G^(0); q^{-1}(G^(0))))` (`prop:effectiveACPprincipalADP`).
5. If `G_1` is effective, twists `Σ_1 → G_1` and `Σ_2 → G_2` are isomorphic iff there is an `R`-algebra isomorphism of
   the twisted Steinberg algebras mapping the first diagonal into the second (`cor:equiv.twist.effective`).

Credit: B. Armstrong, G. G. de Castro, L. O. Clark, K. Courtney, Y.-F. Lin, K. McCormick, J. Ramagge, A. Sims,
B. Steinberg, *Reconstruction of twisted Steinberg algebras*, Int. Math. Res. Not. IMRN 2023, 2474–2542,
doi:10.1093/imrn/rnab291 (checked on Crossref), arXiv:2101.08556. The labels are those of the arXiv source; the verbatim
text is in the `-citation` route. Remark (3) after `def:ACP` in the source says that existence and uniqueness of such
subalgebras "are natural and interesting questions, though they are not addressed in this paper".

Use: `subshift-ring-cartan-uniqueness-iff-groupoid-model-rigidity`.
