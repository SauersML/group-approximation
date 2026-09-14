---
rg: 2
id: fsp-graph-of-rings-and-linnell-extension-citation
kind: route
title: Import the characteristic-free graph-of-rings and Linnell extension corollaries of Fisher--Sanchez-Peralta
target: fsp-graph-of-rings-and-linnell-extension-imports
requires: []
artifacts:
  - research/artifacts/gk3-nonrf-hosts-2026-09-14.md
---

**Source.** S. P. Fisher and P. Sánchez-Peralta, *Division rings for group algebras of virtually compact special
groups and 3-manifold groups*, arXiv:2303.08165v4 (20 Feb 2025), <https://arxiv.org/abs/2303.08165>. The TeX
source (`main.tex`) was downloaded from the arXiv e-print endpoint on 2026-09-14 and read directly. TeX labels
are given because compiled numbers were not extracted, except Proposition 3.14, which main already cites.

**Item 1**, Section "Hughes-free and Linnell division rings", verbatim: "Ian Hughes showed that when Hughes-free
division rings exist, they are unique up to $k * G$-isomorphism \cite{HughesDivRings1970}." and "If $H$ is a
subgroup of $G$, note that the division closure of $k * H$ in $\mathcal D_{k*G}$ is Hughes-free as a
$k*H$-division ring, and therefore we have a natural inclusion $\mathcal D_{k*H} \subseteq \mathcal D_{k*G}$."
The definitions (HF) and (L) are `def:HF` there, copied in the claim.

**Item 2**, `thm:HFresults`, citing Jaikin-Zapirain, *The universality of Hughes-free division rings*, Selecta
Math. 27 (2021), Theorem 1.1: "Let $G$ be a locally indicable amenable group, a residually (torsion-free
nilpotent) group, or a free-by-cyclic group. Then $\mathcal D_{k * G}$ exists and it is universal." The sentence
before it: "Since RAAGs are residually (torsion-free nilpotent) (\cite{Droms_thesis} and
\cite{DuchampKrob_RAAGsRTFN}), so are their subgroups".

**Item 3**, verbatim: "It is clear that if $G$ is locally indicable and $k*G \hookrightarrow \mathcal D$ is a
Linnell embedding, then it is also a Hughes-free embedding."

**Item 4**, `lem:twisted_ext`: "Let $G$ be a group and let $H \trianglelefteqslant G$ be a locally indicable normal
subgroup. Fix a crossed product structure $k*G$ for some division ring $k$. If there is a Hughes-free embedding
$\varphi \colon k*H \hookrightarrow \mathcal D_{k*H}$, then we can form $\mathcal D_{k*H} * [G/H]$ and there is a
natural embedding $k*G \cong (k*H) * [G/H] \hookrightarrow \mathcal D_{k*H} * [G/H]$." The proof extends
automorphisms by Hughes uniqueness.

**Item 5**, `cor:HF_fi`: "Let $k*G$ be a crossed product of a torsion-free group $G$ and a division ring $k$.
Suppose $H \trianglelefteqslant G$ is a normal and locally indicable subgroup such that $G/H$ is elementary
amenable. If there is a Hughes-free embedding $k*H \hookrightarrow \mathcal D_{k*H}$ and
$\mathcal D_{k*H}*[G/H]$ is a domain, then embedding $k*G \hookrightarrow \Ore(\mathcal D_{k*H}*[G/H])$ is
Linnell and is unique among Linnell embeddings up to $k*G$-isomorphism." Its proof uses Gräter's theorem that
Hughes-free division rings are Linnell (`thm:grater`, Gräter, Forum Math. 32 (2020), Corollary 8.3) and
`lem:LinnellFIovergroup`, whose proof was read.

**Item 6**, `cor:locIndGraphDivRing`: "Let $k$ be a division ring, let $\mathscr G_\Gamma = (G_v, G_e)$ be a graph of
locally indicable groups, and fix a crossed product $k * \mathscr G_\Gamma$. Suppose there is a Hughes-free
embedding $k * G_v \hookrightarrow \mathcal D_{k * G_v}$ for each vertex $v$ of $\Gamma$. Then
$k * \mathscr G_\Gamma$ embeds in a division ring." It rests on `prop:kGinjects` (normal forms, Dicks Theorems
34(i), 35(i)) and `thm:graphOfHF` (coproducts of semifirs over a division ring are semifirs, Cohn and Dicks;
semifirs embed in division rings, Cohn, *Free Ideal Rings and Localization*, Corollary 7.5.14).

**Characteristic.** The Higman proposition (`Proposition 3.14`, lines 519–529 of `main.tex`) begins "Let $k$ be a
field of characteristic $0$" and obtains the vertex embeddings "by \cite[Corollary 1.4]{JaikinLopez_Atiyah}".
None of items 1–6 assumes a characteristic.

**Trust surface.** Statements and the proofs of items 4–6 were read in the TeX source. The deeper inputs (Hughes
1970; Gräter 2020; Linnell--Schick, Lemma 2.5; Dicks, Theorems 34–35; Cohn; Jaikin-Zapirain, Theorem 1.1;
Droms; Duchamp--Krob) were not reread. QED
