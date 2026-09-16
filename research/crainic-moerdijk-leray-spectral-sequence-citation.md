---
rg: 2
id: crainic-moerdijk-leray-spectral-sequence-citation
kind: route
title: Import of Crainic–Moerdijk 2000, 3.1, 3.5, 4.1–4.5, on étale groupoid homology and its Leray spectral sequence
target: crainic-moerdijk-groupoid-leray-spectral-sequence
requires: []
artifacts:
  - research/artifacts/cantor-configuration-modules-v-acyclic-germ-groupoid-2026-09-16.md
---

**Source.** M. Crainic and I. Moerdijk, *A homology theory for étale groupoids*, J. reine
angew. Math. 521 (2000), 25–46, arXiv:math/9905011.

**How it was read.** On 2026-09-16 the arXiv e-print TeX source (v1) was fetched and
gunzipped into the session scratchpad as `cm/homology.tex`. The quotes below come from that
file.

**Numbering.** The file declares `\newtheorem{st}{Theorem}[section]`, and `prop`, `lem`,
`cor`, `defin`, `exam` and the unnamed `num` environment share the `st` counter. The
section and item numbers below were counted from the file, so they are not independent
checks. Two outside sources agree with them.
- H. Matui, *Homology and topological full groups of étale groupoids on totally disconnected
  spaces*, Proc. London Math. Soc. 104 (2012), arXiv:0909.1624. Matui cites "[CM, Theorem
  4.4]" for this spectral sequence.
- Matui introduces the same homology theory as the constant-coefficient case of [CM]. His
  TeX source (arXiv:0909.1624, read 2026-09-16, `m12.tex` l.357–364) says: "We briefly
  recall homology theory for \'etale groupoids which was studied in \cite{CM}. [...] Here,
  we restrict our attention to the case of constant coefficients and introduce homology
  groups in an elementary way". His definition is the complex `C_c(G^(n), A)` with
  `δ_1 = s_* − r_*`. This matches 3.1 with the c-soft constant sheaf.

**Verbatim.**
- 3.1 (TeX l.490 ff.): "Let $\A$ be a $\G$-sheaf, and assume that $\A$ is c-soft as a sheaf
  on $\nG{0}$ [...] The groups $\Gamma_{c}(\nG{n}, \A_{n})$ of compactly supported sections
  [...] together form a simplicial abelian group" and "The homology groups $H_{n}(\G; \A)$
  are defined as the homology groups of the simplicial abelian groups".
- 3.5(2) (TeX l.575): "If $\G$ is a discrete groupoid, $\nG{\cdot}$ is a simplicial set, and
  $H_{n}(\G; \A)$ is the usual simplicial homology of $\nG{\cdot}$ with twisted
  coefficients."
- 4.1, comma groupoids (TeX l.743): "For each point $x \in \nG{0}$ consider the ``comma
  groupoid'' $x/\f$, whose objects are the pairs $(y, g: x \rmap \f(y))$ where
  $y\in \nK{0}$ and $g\in \nG{1}$. An arrow $k: (y, g) \rmap (y', g')$ in $x/\f$ is an arrow
  $k: y\rmap y'$ in $\Ka$ such that $\f(k)\compose g= g'$. When equipped with the obvious
  fibered product topology, $x/\f$ is again an \'etale groupoid."
- 4.2: "$B_{n}(\f ; \A ) = (\beta_{n})_{\, !}\alpha_{n}^{\, * } \A$" and "$L_{n}\f_{\, !}(-)
  = \Ha_{n}(\el \f_{\, !}(-))$".
- Proposition 4.3 (TeX l.790–794): "For any $x \in \nG{0}$, there are isomorphisms:
  $(L_{n}\f_{\, !}(\A))_{x} \cong H_{n}( x/\f; \pi_{x}^{*}\A )$ for all $x \in \nG{0}$."
- Theorem 4.4 (TeX l.805–809): "(``Leray-Hochschild-Serre spectral sequence'') For any
  homomorphism $\f: \Ka \rmap \G$ between \'etale groupoids and any $\Ka$-sheaf $\A$ there
  is a natural spectral sequence: $E_{p,q}^{2} = H_{p}(\G; L_{q}\f_{\, !}\A )
  \Longrightarrow H_{p+q}(\Ka; \A)$."
- 4.5(2) (TeX l.855): "If $\f: \Ka \rmap \G$ is \'etale, $\es \in \abK$, then there is no
  need of c-soft resolutions to define $\el\f_{\, !}\es$. Indeed, the condition on $\f$
  implies that the maps $\beta_n$ defined in \ref{flosr} are \'etale, so there is a
  quasi-isomorphism $\el\f_{\, !}\es \simeq B_{\cdot}(\f; \es)$."
- 3.7(2): "Suppose $\f$ is \'etale, in the sense that each $\f_{n}: \nK{n} \rmap \nG{n}$ is a
  local homeomorphism (it is not difficult to see that the assumption is only about
  $\f_0$)."

**Scope.** The import is used only for groupoids whose unit spaces are second countable,
totally disconnected, locally compact and Hausdorff. Such spaces satisfy the paper's standing
assumptions, with cohomological dimension 0, and every sheaf of abelian groups on them is
c-soft.
