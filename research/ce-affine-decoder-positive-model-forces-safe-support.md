---
rg: 2
id: ce-affine-decoder-positive-model-forces-safe-support
kind: claim
title: Any positive CE corner model forces affine-safe support for a universally CE-exact affine decoder
distinct_from:
  ce-exact-affine-compilers-force-nonhyperlinear-corners: that assumes the whole ambient group hyperlinear to obtain its canonical model; this starts from any CE corner model and passes to its hyperlinear image quotient, excluding a positive CE model even for a nonhyperlinear host on affine-unsafe sources
  group-corner-exact-compilers-force-source-affine-safety: that assumes exactness on every tracial model; this only uses exactness on CE models, together with existence of one such model
artifacts:
  - research/artifacts/ce-affine-quotient-audit-2026-09-20.md
---

Let Gamma be countable, J central of finite order n, and omega a faithful
character of <J>. Suppose a finite BCS has an affine decoder through
finite abelian contexts of p_omega C*(Gamma), exact on every CE tracial
model, in the precise sense of
`ce-exact-affine-compilers-force-nonhyperlinear-corners`.

If this corner admits any CE tracial model, then the source BCS admits a
perfect CE model whose support in every context is affine and contained
in that context's allowed answer set. Gamma itself need not be hyperlinear.

Thus if the source has no affine-safe perfect CE model, the target corner
has no CE model. A nonhyperlinear host alone cannot evade this conclusion.
The claim does not cover non-affine or constant-loss decoders.
