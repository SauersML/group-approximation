---
rg: 2
id: genus-two-mapping-class-group-homology-citation
kind: route
title: Import finite presentation and low-degree homology of Mod(S_2) from Korkmaz's survey and the symplectic sequence from the Wikipedia mapping class group article
target: genus-two-mapping-class-group-homology-and-symplectic-quotient
requires: []
---

Sources were fetched on MSI into `/scratch.global/sauer354/hl-nh-deligne-torus/src/` on 2026-09-13.

## Korkmaz, "Low-dimensional homology groups of mapping class groups: a survey", arXiv:math/0307111

File `survey.tex`, verbatim. The macro `\M` is `{\Gamma }` (l.17), and `\M_g` is the mapping class
group of the closed genus-`g` surface.

- **Definition** (l.53–55): "The mapping class group of $\Sigma_{g,r}^n$ … is defined as the group of
  the isotopy classes of orientation-preserving diffeomorphisms".
- **Item 1** (l.285): "The mapping class groups are finitely presented."
- **Item 2** (l.386–388): "the group $H_1(\M_g;\Z)$ can be computed easily; it is isomorphic to
  $\Z_{10}$ if $g=2$ and $0$ if $g\geq 3$. The fact that $H_1(\M_2;\Z)$ is isomorphic to $\Z_{10}$ was
  first proved by Mumford~\cite{mu}".
- **Item 3** (l.595–599): "The same method above also proves that $H_2(\M_2;\Z)=H_2(\M_{2,1};\Z)$ is
  isomorphic to either $0$ or $\Z_2$, … By the work of Benson-Cohen~\cite{bc}, $H_2(\M_2;\Z_2)$ is
  isomorphic to $\Z_2\oplus\Z_2$. It follows now from the universal coefficient theorem that
  $H_2(\M_2;\Z)$ is not trivial, hence $\Z_2$."

## Wikipedia, "Mapping class group", raw wikitext (`action=raw`)

File `mcg-wiki.txt`, verbatim.

- **Kernel** (l.80): "The kernel of this action is the ''Torelli group'', named after the
  [[Torelli theorem]]."
- **Surjectivity** (l.82–83): "''H''<sup>1</sup>(Σ) has a [[Symplectic geometry|symplectic]]
  structure, coming from the [[cup product]]; since these maps are automorphisms, and maps preserve
  the cup product, the mapping class group acts as symplectic automorphisms, and indeed all symplectic
  automorphisms are realized, yielding the [[short exact sequence]]:
  :<math>1 \to \operatorname{Tor}(\Sigma) \to \operatorname{MCG}(\Sigma) \to
  \operatorname{Sp}(H^1(\Sigma)) \cong \operatorname{Sp}_{2g}(\mathbf{Z}) \to 1</math>".
  This gives item 4 at `g = 2`.

## Cross-check of the kernel definition

Brendle–Margalit–Putman, arXiv:1211.4018v4, p. 1: "The Torelli group $\mathcal{I}_g$ is the kernel of
the action of $\mathrm{Mod}_g$ on $H_1(\Sigma_g;\mathbb{Z})$".
