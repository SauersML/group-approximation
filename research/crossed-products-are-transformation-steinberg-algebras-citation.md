---
rg: 2
id: crossed-products-are-transformation-steinberg-algebras-citation
kind: route
title: Literature import of Beuter–Gonçalves (arXiv:1706.00127) - partial skew group rings of locally constant functions are Steinberg algebras of transformation groupoids
target: crossed-products-are-transformation-steinberg-algebras
requires: []
artifacts:
  - research/artifacts/un-review3-2026-09-13-part1.md
---

**Source.** V. M. Beuter and D. Gonçalves, *The interplay between Steinberg algebras and partial skew rings*,
J. Algebra 497 (2018) 337–362, arXiv:1706.00127. The arXiv TeX source (`SteinAlgSkewRingInvSemig.tex`) was
fetched with curl on MSI on 2026-09-13 and read at lines 28–34 (macros), 394 and 442–444.

**Standing assumption, verbatim (l.394).** "In this section we prove that partial skew group rings of the form
$\mathcal{L}_c(X)\rtimes_{\alpha} G$ can be realized as Steinberg algebras. This result is attributed to folklore
and we provide a proof of it here. Throughout we assume that $R$ is a commutative ring with unit, and $X$ is a
Hausdorff, locally compact, totally disconnected topological space."

**Theorem `theorisomortransfgrou`, verbatim with macros expanded (l.442–444).** "Let
$\theta=(\{X_g\}_{g \in G}, \{\theta_g\}_{g \in G})$ be a partial action of a discrete group $G$ over a locally
compact, Hausdorff, totally disconnected topological space $X$, such that each $X_g$ is clopen. Let
$(\{D_g\}_{g \in G}, \{\alpha_g\}_{g\in G})$ be the corresponding partial action (as defined above) and
$G \ltimes_\theta X$ be the transformation groupoid associate with $\theta.$ Then
$\mathcal{L}_c(X)\rtimes_{\alpha} G$ and $A_R(G \ltimes_\theta X)$ are isomorphic as $R$-algebras."

**Why sufficient for the target.**
- The target is the global-action case: `X_g = X` for every `g`, so `D_g = L_c(X)`, and the partial skew group ring
  is the skew group ring `LC(X,R) ⋊ Γ`.
- `X` compact means `L_c(X) = LC(X,R)`.
- Conventions differ only by inversion. In the source, `r(t,x) = (1,x)` and `s(t,x) = (1, θ_(t^(-1))(x))` (l.426), with
  `ρ(f_g δ_g)(t,x) = f_g(x)` on the sheet `t = g`. The target's map `Ψ(f u_γ)(γ,x) = f(γx)` uses arrows with source
  `x` and range `γx`. The two groupoids are isomorphic through `(γ, x) ↦ (γ, γx)`, compatibly with the two maps.
- The source attributes the result to folklore. The lane's own proof (`crossed-products-are-transformation-steinberg-algebras-proof`)
  stays as an independent second route.

**Not verified here.** The journal theorem number, and the algebraic partial action construction (`D_g`, `α_g`)
beyond the global case.
