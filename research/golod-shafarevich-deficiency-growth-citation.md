---
rg: 2
id: golod-shafarevich-deficiency-growth-citation
kind: route
title: Import Ershov's presentation test for Golod–Shafarevich groups and their uniformly exponential growth
target: golod-shafarevich-deficiency-test-and-exponential-growth
requires: []
artifacts:
  - research/artifacts/hl-fp-intermediate-growth-2026-09-14.md
---

Literature import.
- **Source.** M. Ershov, *Golod–Shafarevich groups: a survey*, arXiv:1206.0490 (Internat. J.
  Algebra Comput. 22 (2012)).
- **Copy read.** TeX source `main.tex`, fetched on MSI on 2026-09-14 under
  `/scratch.global/sauer354/hl-fp-intermediate-growth/src/1206.0490/`.
- **Pins.** Verbatim pins are in `research/artifacts/hl-fp-intermediate-growth-2026-09-14.md`.

**Item 1** is Theorem `GS_strong`(b) (l.1078–1081): "Let $\Gamma=\la X|R \ra $ be a finitely
presented abstract group, and let $d_p(\Gamma)=\dim_{\Fp}(\Gamma/[\Gamma,\Gamma]\Gamma^p)$. If
$|R|<d_p(\Gamma)^2/4-d_p(\Gamma)+|X|$ and $d_p(\Gamma)>1$, then $\Gamma$ is Golod-Shafarevich (with
respect to $p$)."
- The survey's definition (l.949–950): "An abstract group $G$ is called a {\it Golod-Shafarevich}
  group (with respect to $p$) if its pro-$p$ completion $G_{\phat}$ is Golod-Shafarevich."
- `Γ/[Γ,Γ]Γ^p ≅ H₁(Γ; F_p)` is the mod-`p` abelianization.

**Item 2** is Proposition `prop:BaGr` (l.1133): "Golod-Shafarevich abstract groups have uniformly
exponential growth."
- The survey's proof uses the numbers `a_n = dim F_p[Γ]/M^{n+1}` (augmentation ideal `M`), which
  grow exponentially by Proposition `gs:filtered`(a).
- The proof ends: "Each such product lies in the $\Fp$-span of $B_X(n)$, the ball of radius $n$
  with respect to $X$ in $\Gamma$. Hence $|B_X(n)|\geq a_n$."

This route asserts only what the survey states.
