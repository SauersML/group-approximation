---
rg: 2
id: local-spectral-expansion-survives-bounded-triangle-removal
kind: claim
title: Removing t triangles from a local spectral expander whose edges lie in at least d triangles raises the link eigenvalue bound by at most (t+sqrt(2t))/(d-t)
distinct_from:
  random-complex-mid-range-pair-properties: that imports local spectral expansion of the random complex itself; this is a deterministic perturbation bound for any complex after removing triangles
  bounded-removal-finite-quotient-caps-cocycle-cheeger: that takes local spectral expansion of the complex minus the removed triangles as a hypothesis; this derives that hypothesis from expansion of the full complex and large edge degrees
---

**ESTABLISHED.** Let `X` be a pure 2-dimensional simplicial complex, with the
uniform measure on its triangles and the descending edge and vertex measures.
Suppose

* every edge of `X` lies in at least `d` triangles, and
* `X` is a λ-local spectral expander.

Let `T ⊂ X(2)` with `|T| = t < d`, and let `X \ T` have the same vertices and
edges as `X` and triangles `X(2) \ T`, again with the uniform triangle measure.
Then `X \ T` is pure. It is a `λ'`-local spectral expander, where

```text
λ' = λ + (t + sqrt(2t)) / (d - t).
```

If `X` is connected, so is `X \ T`, because the 1-skeleton is unchanged.

**Convention.** This is Chapman--Peled's definition (arXiv:2509.21566v2,
`Random.tex`, §2 "Local spectral expansion", read from the TeX on MSI on
2026-09-13):

> We say that $\cX$ is a \emph{$\lambda$-spectral expander} if the second
> eigenvalue of $A$ is bounded by $\lambda$ from above. We say that $\cX$ is a
> \emph{$\lambda$-local spectral expander} if the links $\cX_v$ are
> $\lambda$-spectral expanders for all $v\in \cX(0)$.

In the same section the link measure is
$\mu_{v,1}(e)=\frac{\mu_2(v\cup e)}{\sum_{e'\in \cX_v(1)}\mu_2(v \cup e')}$. The
link vertex measure descends from it, and $Af(v)=\Ex_{u\sim \mu_{v,0}}[f(u)]$.

Derivation: `bounded-triangle-removal-link-perturbation-proof`. No novelty is
claimed. This is a matrix perturbation argument.
