---
rg: 2
id: random-groups-no-fixed-degree-representations-citation
kind: route
title: Import Kozma–Lubotzky's fixed-degree representation theorem for Gromov random groups
target: random-groups-have-no-fixed-degree-linear-representations
requires: []
artifacts:
  - research/artifacts/solve-hyperbolic-rf-simple-quotients-2026-09-13.md
---

**Source.** G. Kozma and A. Lubotzky, *Linear representations of random groups*,
arXiv:1810.01529 (Bull. Math. Sci. 2019). The arXiv e-print was fetched on MSI on 2026-09-13
(`nosl3.tex`, 763 lines, md5 `b9aa69e9ea17bdfd753a26dec3c898ad`).

**Verbatim.**
- **Model (l.143–154):** "let $R$ be a random subset of $S_{l}$ constructed by taking
  $\lfloor|S_{l}|^{d}\rfloor=\lfloor\big(2m(2m-1)^{l-1}\big)^{d}\rfloor$ elements of $S_{l}$
  uniformly, independently and with repetitions."
- **`thm:d` (l.160–164):** "Let $k\ge1$, $m\ge2$ and $d>0$. Then Gromov random groups
  $\Gamma$ at density $d$ with $m$ generators satisfy a.a.s.\ that for any field $F$ and any
  $\rho:\Gamma\to\mathrm{GL}_{k}(F)$, $|\rho(\Gamma)|\le2$."
- **`thm:poly` (l.630–641):** "Let $R$ be be given by taking at least $(3l)^{7m^{2}k^{4}}$
  random reduced words of length $l$ … independently, uniformly, with repetitions. …
  Then $\lim_{l\to\infty}\mathbb{P}(\exists F,\rho:\Gamma\to\mathrm{GL}_{k}(F)\text{ such
  that }|\rho(\Gamma)|>2)=0$ where $F$ runs over the all fields".
- **`lem:one F` (l.562–573):** the single-field bound
  $\exp(-cu/mk^{2})$ for $u\ge15m^{3}k^{4}\log l$ relators and $l>l_{0}(k,m)$.
- **Odd length (l.169–171):** "When $l$ is odd, it is easy to see that
  $\mathbb{Z}/2\mathbb{Z}$ is a.a.s.\ not a quotient of $\Gamma$ hence in fact we may
  strengthen Theorem \ref{thm:d} to state that $\rho(\Gamma)=\{1\}$."

The full passages are in the artifact.

**Match.** Items 1–3 of the target restate these, in the source's notation. The source's
proof (the section from l.489) was read but not re-derived. It uses its own Bézout theorem
(l.257–262) and an effective Nullstellensatz citing Brownawell (l.424–437); neither was
re-checked.
