---
rg: 2
id: interpolated-free-group-factor-compression-formula
kind: claim
title: Amplifications of interpolated free group factors are interpolated free group factors
artifacts:
  - research/artifacts/hl-free-group-factors-2026-09-13.md
---

For `1 < r <= infinity` and `0 < gamma < infinity`,

```text
L(F_r)_gamma  =  L(F_{1 + (r-1)/gamma^2}),
```

where `M_gamma` is the amplification (compression for `gamma <= 1`) of a II_1
factor, with `(M_{gamma_1})_{gamma_2} = M_{gamma_1 gamma_2}`. In particular all
`L(F_r)` with `1 < r < infinity` are amplifications of one another:
`L(F_s) = L(F_r)_gamma` with `gamma = sqrt((r-1)/(s-1))`.

Literature import, verbatim from the TeX source of K. Dykema, *Interpolated free
group factors* (arXiv:funct-an/9211012; Pacific J. Math. 163 (1994)), fetched on
MSI 2026-09-13:

- l.440–441: "\proclaim{Theorem 2.4} $$ L(\freeF_r)_\gamma=L(\freeF(1+\frac{r-1}{\gamma^2})) \tag9 $$ for $1<r\le\infty$ and $0<\gamma<\infty$."
- l.145–150: "for $0<\gamma\le1$, $\MvN_\gamma=p\MvN p$, where $p\in\MvN$ is a self--adjoint projection of trace $\gamma$; for $\gamma=n=2,3,\ldots$ one has $\MvN_\gamma=\MvN\otimes M_n(\Cpx)$; for $0<\gamma_1,\gamma_2<\infty$ one has $$\MvN_{\gamma_1\gamma_2}= (\MvN_{\gamma_1})_{\gamma_2}. $$"
- l.427–436 credit the formula to Voiculescu for special cases and to Rădulescu in
  full generality.

Trust surface: refereed, statement-level use only; the proof was not re-read.
