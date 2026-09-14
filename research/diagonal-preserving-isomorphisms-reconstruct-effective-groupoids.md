---
rg: 2
id: diagonal-preserving-isomorphisms-reconstruct-effective-groupoids
kind: claim
title: A ring isomorphism of Steinberg algebras over an indecomposable ring that maps the diagonal into the diagonal forces the groupoids to be isomorphic, when one of them is effective Hausdorff ample
---

Let `R` be an indecomposable commutative ring with unit, and let `𝒢, 𝒢'` be Hausdorff ample groupoids with `𝒢`
effective. The following are equivalent:
1. `𝒢 ≅ 𝒢'` as topological groupoids;
2. there is a diagonal-preserving ring isomorphism `R𝒢 → R𝒢'`;
3. there is a ring isomorphism `Φ: R𝒢 → R𝒢'` with `Φ(D(𝒢)) ⊆ D(𝒢')`.

Here `D(𝒢)` is the algebra of compactly supported locally constant functions on the unit space. No hypothesis on `𝒢'`
is needed.

Credit: B. Steinberg, *Diagonal-preserving isomorphisms of étale groupoid algebras*, J. Algebra 518 (2019), 412–439,
doi:10.1016/j.jalgebra.2018.10.024 (checked on Crossref), arXiv:1711.01903. This is Corollary `c:effective.case.gpd.rec`
of the arXiv source, taken with the trivial grading group, as the source allows ("Theorem~\ref{t:main} applies to the
ungraded setting by taking G to be trivial"). The verbatim text is in the `-citation` route.

Use: `subshift-ring-cartan-uniqueness-iff-groupoid-model-rigidity`.
