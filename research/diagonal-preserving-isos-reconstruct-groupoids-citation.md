---
rg: 2
id: diagonal-preserving-isos-reconstruct-groupoids-citation
kind: route
title: Import of Steinberg's diagonal-preserving reconstruction theorem for effective ample groupoids
target: diagonal-preserving-isomorphisms-reconstruct-effective-groupoids
requires: []
---

Source: B. Steinberg, *Diagonal-preserving isomorphisms of étale groupoid algebras*, J. Algebra 518 (2019), 412–439,
doi:10.1016/j.jalgebra.2018.10.024. The text below was read from the arXiv source of arXiv:1711.01903, `main.tex`,
extracted on MSI (lane sk-rigidity-cartan, 2026-09-13).

Verbatim, `main.tex` l.656–666 (Theorem `t:main`):

> Let $R$ be an indecomposable commutative ring with unit and let $\mathscr G$, $\mathscr G'$ be Hausdorff ample
> $G$-graded groupoids. Suppose that $\mathscr G$ has a dense set of objects $x$ such that the group algebra over $R$ of
> the isotropy group at $x$ of the interior of the isotropy bundle of the homogeneous component of $1$ has no
> non-trivial units. Then the following are equivalent. (1) There is a graded isomorphism
> $\p\colon \mathscr G\to \mathscr G'$. (2) There is a diagonal-preserving graded isomorphism
> $\Phi\colon R\mathscr G\to R\mathscr G'$ of $R$-algebras. (3) There is a diagonal-preserving graded isomorphism
> $\Phi\colon R\mathscr G\to R\mathscr G'$ of rings.

Verbatim, l.668 (after the theorem): "Of course, Theorem~\ref{t:main} applies to the ungraded setting by taking $G$ to
be trivial."

Verbatim, Corollary `c:effective.case.gpd.rec`:

> Let $R$ be an indecomposable commutative ring with unit and let $\mathscr G$ and $\mathscr G'$ be $G$-graded Hausdorff
> ample groupoids. Suppose that $\mathscr G_1$ is effective. Then the following are equivalent. (1) There is a graded
> isomorphism $\p\colon \mathscr G\to \mathscr G'$. (2) There is a diagonal-preserving graded isomorphism
> $\Phi\colon R\mathscr G\to R\mathscr G'$ of $R$-algebras. (3) There is a diagonal-preserving graded isomorphism
> $\Phi\colon R\mathscr G\to R\mathscr G'$ of rings. (4) There is a graded $R$-algebra isomorphism
> $\Phi\colon R\mathscr G\to R\mathscr G'$ with $\Phi(D(\mathscr G))\subseteq D(\mathscr G')$. (5) There is a graded ring
> isomorphism $\Phi\colon R\mathscr G\to R\mathscr G'$ with $\Phi(D(\mathscr G))\subseteq D(\mathscr G')$.

Verbatim, the note following the proof: "Notice that in~\cite{reconstruct} both groupoids are assumed to have a
topologically principle homogeneous component of $1$, whereas our result only requires that $\mathscr G_1$ is
effective: no assumption is made on $\mathscr G'_1$."

With the trivial grading group, `𝒢_1 = 𝒢` and "graded" is vacuous. This gives the target claim.
