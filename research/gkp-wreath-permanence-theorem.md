---
rg: 2
id: gkp-wreath-permanence-theorem
kind: claim
title: A generalized wreath product of sofic groups over a sofic action is sofic
distinct_from:
  gkp-sofic-action-toolkit: that imports Theorem 2.14 and Propositions 2.15-2.16 of the same paper (restriction, orbits, locally finite kernels); this imports the wreath-product permanence theorem, Theorem 3.6, which coordinate-action-not-sofic consumes as the second half of its contradiction and which no node carried before.
  kun-thom-nonsofic-wreath: that is the NON-soficity theorem for wreath products over infranormal Kazhdan pairs; this is the positive permanence theorem whose hypotheses the Kun--Thom coset action must therefore fail.
---

**Literature input (source re-read 2026-08-22, arXiv:2401.04945v3 HTML).**
Gao--Kunnawalkam Elayavalli--Patchell, *Soficity for group actions on sets
and applications*, Res. Math. Sci. 12 (2025) 48, arXiv:2401.04945.

Definition 3.1: for groups `G, H` and an action `alpha : H -> Sym(X)`, the
generalized wreath product is

```text
G wr_alpha H = G^(+X) rtimes_beta H,     beta(h)((g_x)_x) = (g_(alpha(h)^(-1) x))_x,
```

with the RESTRICTED direct sum `G^(+X)` (finitely supported lamps).

Definition 2.1(5): `alpha : H -> Sym(X)` is a sofic action if for all finite
`F subset H`, `E subset X` and `epsilon > 0` there are a finite set `A` and a
unital `(F, epsilon)`-multiplicative map `phi : H -> Sym(A)` that is an
`(F, E, epsilon)`-orbit approximation of `alpha`.

> **Theorem 3.6.**  Let `G, H` be sofic groups and `alpha : H -> X` a
> sofic action.  Then the generalized wreath product `G wr_alpha H` is
> sofic.

Three hypotheses and nothing else: `G` sofic, `H` sofic, `alpha` sofic in
the sense of Definition 2.1(5).  Used by `coordinate-action-not-sofic-proof`
with `G = Z/2`, `H` the Kun--Thom group, `X = H/Gamma`.
