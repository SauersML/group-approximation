---
rg: 2
id: semilocal-steinberg-groups-have-central-k2-citation
kind: route
title: Voronetsky's semilocal crossed-module theorem, and Tulenbaev for finite algebras
target: semilocal-steinberg-groups-have-central-k2
requires: []
artifacts:
  - research/artifacts/sk-free-4-finite-simple-shadows-2026-09-13-part4.md
---

Source read this session: E. Voronetsky, *Centrality of K_2-functor revisited*, J. Pure Appl. Algebra 225:4 (2021),
arXiv:2004.08551, TeX source `1.tex`, fetched on MSI.
- **l.401–402**, theorem labelled `SemilocalCrossedModule`: "Let \(R\) be a semi-local unital ring with a complete
  family of Morita equivalent orthogonal idempotents \(e_1, \ldots, e_n\). Suppose that \(n \geq 3\). Then there is
  unique action of \(\glin(R)\) on \(\stlin(R)\) making \(\stmap \colon \stlin(R) \rar \glin(R)\) a crossed module".
- **l.113:** "For every crossed module the kernel of \(d\) is a central subgroup of \(H\)".
- **l.76:** "M.\,S. Tulenbaev extended this result to all finite \(K\)-algebras". Bibliography:
  "Schur multiplier of the group of elementary matrices of finite order. J. Sov. Math., 17(4):2062--2067, 1981."

Apply it to `R = M_n(A)`, `e_i = e_ii`, with `A` semilocal (then `M_n(A)` is semilocal). The Steinberg group of this
idempotent family is `St_n(A)` (the paper's convention; recalled).

Not checked: the printed theorem number in the journal, and Tulenbaev's paper itself.
