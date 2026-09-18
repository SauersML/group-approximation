---
rg: 2
id: pansu-differentiability-of-lipschitz-carnot-maps
kind: claim
title: "Pansu's theorem: a Lipschitz map between Carnot groups is Pansu differentiable almost everywhere, with a group linear differential"
---

Let `G`, `G~` be Carnot groups (simply connected, stratified Lie algebra),
with Carnot–Carathéodory distances `d`, `d~` and dilations `δ_r`, `δ~_r`. A
map `L : G → G~` is *group linear* if `L(xy) = L(x)L(y)` and
`L(δ_r x) = δ~_r L(x)` for all `x, y ∈ G` and `r > 0`. A map `f : G → G~` is
*Pansu differentiable at `x`* if some group linear `L` satisfies
`lim_{h→0} d~(f(x)^{-1} f(xh), L(h)) / d(h) = 0`, where `d(h) = d(e,h)`.

**Statement.** Every Lipschitz `f : (G,d) → (G~,d~)` is Pansu differentiable
at almost every point of `G`, with respect to Haar measure. In coordinates,
Haar measure is a constant multiple of Lebesgue measure.

Only the case `G~ = R^n` (step one, Euclidean distance, addition) is used on
this graph. There the condition reads
`|f(xh) − f(x) − L(h)| = o(d(h))`.

Imported from Pinamonti–Speight, arXiv:1603.04818, Theorem 2.6 (Pansu):
route `pansu-differentiability-of-lipschitz-carnot-maps-citation`.
