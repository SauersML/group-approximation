---
rg: 2
id: lueck-mapping-tori-and-homology-invariance-citation
kind: route
title: Import the cellular lemma, homology invariance and the mapping-torus theorem of Lück's algebraic survey
target: lueck-mapping-tori-and-homology-invariance
requires: []
artifacts:
  - research/artifacts/hl-one-cell-l2-2026-09-14.md
---

W. Lück, *L²-Invariants from the Algebraic Point of View*, arXiv:math/0310489. Read from the TeX
source `ltwoalg.tex`, fetched on MSI on 2026-09-14 into `/scratch.global/sauer354/hl-one-cell-l2/`.
Quotes are verbatim TeX.

- **Definitions, l.1127–1178.**
  - "The \emph{singular homology} $H_p^G(X;\caln(G))$ \emph{of $X$ with coefficients in} $\caln(G)$ is
    the homology of the $\caln(G)$-chain complex $\caln(G) \otimes_{\bbZ G} C_*^{\sing}(X)$ [...]
    $$b_p^{(2)}(X;\caln(G)) ~ := ~ \dim_{\caln(G)}\left(H_p^G(X;\caln(G))\right) \quad \in [0,\infty]$$"
  - "Define for any (discrete) group $G$ its \emph{$p$-th $L^2$-Betti number} by
    $$b^{(2)}_p(G) ~ := ~ b^{(2)}_p(EG,\caln(G)).$$" (item 4)
- **Lemma `singular = cellular`, l.1292–1297.** "Let $X$ be a $G$-$CW$-complex. Let $C_*^c(X)$ be
  its cellular $\bbZ G$-chain complex. Then there is a $\bbZ G$-chain homotopy equivalence
  $C_*^{\sing}(X) \to C_*^c(X)$ and we get $$b_p^{(2)}(X;\caln(G)) ~ = ~
  \dim_{\caln(G)}\left(H_p\left(\caln(G) \otimes_{\bbZ G} C_*^c(X)\right)\right).$$" (item 1)
- **Theorem "$L^2$-Betti numbers for arbitrary spaces", item "Homology invariance" (a),
  l.1317–1345.** "We have for a $G$-map $f\colon X \to Y$: [...] Suppose for $n \ge 1$ that for each
  subgroup $H \subseteq G$ the induced map $f^H\colon X^H \to Y^H$ is $\bbC$-homologically
  $n$-connected, i.e. the map $$H_p^{\sing}(f^H;\bbC)\colon H_p^{\sing}(X^H;\bbC) \to
  H_p^{\sing}(Y^H;\bbC)$$ induced by $f^H$ on singular homology with complex coefficients is
  bijective for $p < n$ and surjective for $p = n$. Then $b_p^{(2)}(X) = b_p^{(2)}(Y)$ for $p < n$;
  $b_p^{(2)}(X) \ge b_p^{(2)}(Y)$ for $p = n$" (item 2)
- **Subsection "Mapping Tori", l.2383–2397.** "There is a canonical map $p\colon T_f \to S^1$ which
  sends $(x,t)$ to $\exp(2\pi i t)$. It induces a canonical epimorphism $\pi_1(T_f) \to \bbZ =
  \pi_1(S^1)$ if $X$ is path-connected. The following result is taken from \cite[Theorem
  6.63]{Lueck(2002)}."
- **Theorem "Vanishing of $L^2$-Betti numbers of mapping tori", l.2398–2415.** "Let $f\colon X \to
  X$ be a cellular selfmap of a connected $CW$-complex $X$ and let $\pi_1(T_f)
  \xrightarrow{\phi} G \xrightarrow{\psi}\bbZ$ be a factorization of the canonical epimorphism
  into epimorphisms $\phi$ and $\psi$. Suppose for given $p \ge 0$ that
  $b_p^{(2)}(G \times_{\phi \circ i} \widetilde{X};\caln(G)) < \infty$ and
  $b_{p-1}^{(2)}(G \times_{\phi \circ i} \widetilde{X};\caln(G)) < \infty$ holds, where $i\colon
  \pi_1(X) \to \pi_1(T_f)$ is the map induced by the obvious inclusion of $X$ into $T_f$. Let
  $\overline{T_f}$ be the covering of $T_f$ associated to $\phi$, which is a free $G$-$CW$-complex.
  Then we get $b_p^{(2)}(\overline{T_f};\caln(G)) = 0.$" (item 3)

Only what the survey states is asserted. Proofs are cited there to Lück's book and to Lück (1998a),
Lemma 4.2, and were not re-derived.
