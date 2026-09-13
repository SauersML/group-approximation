---
rg: 2
id: minimal-effective-steinberg-algebras-have-scalar-centre
kind: claim
title: The Steinberg algebra of a minimal effective ample groupoid with compact unit space has centre k
artifacts:
  - research/artifacts/un-steinberg-elementary-simplicity-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `k` be a field and `𝒢` a Hausdorff ample groupoid with compact unit space that is
effective and minimal. Then `Z(A_k(𝒢)) = k·1`.

Why (artifact §2): a central `z` satisfies `χ_(𝒢⁽⁰⁾∖U) z χ_U = 0` for every clopen `U`, so it is supported on the
isotropy. Its support is open, hence inside the interior of the isotropy, which is `𝒢⁽⁰⁾` by effectiveness. Commuting
with bisection indicators makes `z` invariant along arrows, and a continuous invariant function is constant when orbits
are dense.

Credit: this is Clark–Edie-Michell, arXiv:1403.4684, Theorem `thm:center`(1), quoted from the TeX source on MSI:
"Let $G$ be a Hausdorff, ample groupoid, and $R$ a commutative ring with identity. (1) Suppose $G$ is effective and
minimal, and $G^{(0)}$ is compact. Then $Z(A_R(G)) = R1_{G^{(0)}}$." The proof route here is self-contained.

**Review (un-verify, 2026-09-13): PASS.** Proof re-derived; the Clark–Edie-Michell quote matches arXiv:1403.4684 `main.tex` lines 578–584. Co-credit: Steinberg, arXiv:1408.6014, Proposition 3.7 (p. 10), states the same centre description. See `research/artifacts/un-review-2026-09-13-part1.md` §2.
