---
rg: 2
id: matui-sft-groupoid-homology-is-k-theory
kind: claim
title: Matui — the groupoid of a one-sided shift of finite type has H_0 = K_0 and H_1 = K_1 of its Cuntz–Krieger algebra and no higher homology
---

**ESTABLISHED (import).** H. Matui, *Homology and topological full groups of étale groupoids on totally
disconnected spaces*, arXiv:0909.1624 (Proc. London Math. Soc. 2012). Read 2026-09-13 from the TeX source
`htfgeg.tex` on MSI (`/scratch.global/sauer354/ex/un-k1-homology/0909.1624/main.tex`, lines 1043–1110).

**Setting, verbatim.** "Let $\sigma$ be a one-sided subshift of finite type on a compact totally disconnected
space $X$. We assume that $\sigma$ is surjective. The étale groupoid $G$ associated with $\sigma$ is given by
$G=\{(x,n,y)\in X\times\Z\times X\mid \exists k,l\in\N,\ n=k{-}l,\ \sigma^k(x)=\sigma^l(y)\}$." Matui records that
$C^*_r(G)$ is the Cuntz–Krieger algebra, and that for an automorphism $\pi$ of $K_0(C^*_r(H))$, $H=\{(x,0,y)\}$,
"$K_0(C^*_r(G))\cong\Coker(\id-\pi)$ and $K_1(C^*_r(G))\cong\ker(\id-\pi)$".

**Theorem `CKHomology`, verbatim.** "When $G$ is the étale groupoid arising from a subshift of finite type,
$H_0(G)\cong K_0(C^*_r(G))$, $H_1(G)\cong K_1(C^*_r(G))$ and $H_n(G)=0$ for all $n\geq2$."

Its proof goes through the Lyndon–Hochschild–Serre spectral sequence of the skew product by `ρ(x,n,y) = n`.
It gives `H_0(G) ≅ Coker(id − π)` and `H_1(G) ≅ ker(id − π)` directly.

**Not imported here.** The identification of `Coker(id − π)`, `ker(id − π)` with `Coker(1 − A^t)`,
`ker(1 − A^t)` on `ℤ^N` for the 0–1 matrix `A` of the shift is Cuntz's classical computation. It is used
downstream only as a recalled input, flagged where it is used.

Route: `matui-sft-groupoid-homology-is-k-theory-citation`.
