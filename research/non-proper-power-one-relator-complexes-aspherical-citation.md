---
rg: 2
id: non-proper-power-one-relator-complexes-aspherical-citation
kind: route
title: Import the one-relator Asphericity Theorem (Cockcroft, Lyndon), pinned verbatim from the Linton–Nyberg-Brodda survey
target: non-proper-power-one-relator-complexes-are-aspherical
requires: []
artifacts:
  - research/artifacts/or-length16-nonfree-residue-2026-09-16.md
---

**Secondary pins, verbatim.** M. Linton and C.-F. Nyberg-Brodda, *The theory of one-relator
groups: history and recent progress*, arXiv:2501.18306v1. The TeX source `main.tex` was read on
2026-09-16.
1. Definitions (source line 1636): "If $\lambda\colon S^1\immerses\Lambda$ is an immersion of a
   cycle, denote by \emph{$\deg(\lambda)$} the maximal degree of a covering map
   $S^1\immerses S^1$ that $\lambda$ factors through. Note that $\deg(\lambda) = 1$ if and only
   if $\lambda_*(1)$ is not a proper power in $\pi_1(\Lambda)$, where here
   $1\in \Z = \pi_1(S^1)$ is a generator."
2. Same paragraph: "An \emph{immersion} of graphs is a combinatorial map that is locally
   injective".
3. Source line 1638: "A \emph{2-complex} will be used throughout to mean a two-dimensional
   CW-complex $X$ in which all attaching maps of 2-cells are combinatorial immersions."
4. Source line 1650: "A natural 2-complex to associate to a one-relator group is its presentation
   complex. That is, the 2-complex with a single 0-cell, a 1-cell for each generator and a single
   2-cell whose attaching map spells out the relator."
5. Source line 1653: "A connected 2-complex $X = (\Lambda, \lambda)$ is a \emph{one-relator
   complex} if $\lambda$ is an immersion of a single cycle."
6. Source lines 1708–1713: "Cockcroft characterised when a one-relator complex is aspherical in
   \cite{Co54}. His proof made use of Lyndon's identity theorem \cite{Ly50}, which we shall cover
   in \cref{sec:homology}." and "\begin{theorem}[Asphericity] \label{aspherical} If
   $X = (\Lambda, \lambda)$ is a one-relator complex, then $X$ is aspherical if and only if
   $\deg(\lambda) = 1$. \end{theorem}"

**The cited primary sources**, as listed in the survey's `main.bbl`, verbatim:
- "W.~H. Cockcroft, \emph{On two-dimensional aspherical complexes}, Proc. London Math. Soc. (3)
  \textbf{4} (1954), 375--384."
- "Roger~C. Lyndon, \emph{Cohomology theory of groups with a single defining relation}, Ann. of
  Math. (2) \textbf{52} (1950), 650--665."

**Matching the hypotheses.** Let `w = x_1 x_2 ⋯ x_L` be nontrivial and cyclically reduced in
`F(X)`, with each `x_j ∈ X^{±1}`, and let `K` be its presentation complex.
1. `Λ = K^{(1)}` is the rose on `X`. Subdivide `S^1` into `L` arcs and let `λ : S^1 → Λ` send the
   `j`-th arc onto the 1-cell of `x_j`, in the direction of its exponent. This is a combinatorial
   map, and `K` is obtained from `Λ` by attaching one 2-cell along `λ`. So `K` is `(Λ, λ)`, with
   `S^1` the single cycle.
2. **`λ` is an immersion.** Each 1-cell `e` of the rose contributes two half-edges at the vertex:
   its initial end `e_-` and its terminal end `e_+`. A path reading `e^{+1}` leaves along `e_-`
   and arrives along `e_+`. A path reading `e^{-1}` leaves along `e_+` and arrives along `e_-`.
   Local injectivity can only fail at the vertex of `S^1` between arcs `j` and `j+1` (indices mod
   `L`). There, the arriving half-edge of `x_j` meets the leaving half-edge of `x_{j+1}`. They
   coincide exactly when `x_{j+1} = x_j^{-1}`. When `L = 1` the only such vertex joins the arc to
   itself, and the two half-edges are `e_+` and `e_-`, which are distinct.
   So `λ` is locally injective if and only if `w` is cyclically reduced. Hence `K` is a
   2-complex in the survey's sense (pin 3), and it is a one-relator complex (pin 5) since `Λ` is
   connected.
3. **`deg(λ) = 1`.** `λ_*(1)` is the conjugacy class of `w` in `π_1(Λ) = F(X)`. By pin 1,
   `deg(λ) = 1` if and only if `w` is not a proper power in `F(X)`, which is the hypothesis.
4. By the Asphericity Theorem (pin 6), `K` is aspherical.

Pin 4 confirms that the survey treats the presentation complex as the natural 2-complex of a
one-relator group. The matching above does not rely on that remark.

**Primary not read.** Neither Cockcroft 1954 nor Lyndon 1950 was read on 2026-09-16. The import
rests on the survey's statement of the Asphericity Theorem. A check against Cockcroft's printed
theorem, or a textbook account of Lyndon's identity theorem, is still outstanding.

**Referee check (2026-09-16).** The referee downloaded the arXiv e-print of 2501.18306v1 again. The
quoted statements match `main.tex` word for word (lines 1636–1713). The bibliography entries match
`main.bbl` (Cockcroft 1954 at line 698, Lyndon 1950 at line 1774). The referee also checked the
hypothesis matching: an immersion is the same as a cyclically reduced relator, and degree 1 is the
same as not a proper power. The primaries were still not read.
