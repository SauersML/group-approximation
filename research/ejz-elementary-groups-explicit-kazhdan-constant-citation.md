---
rg: 2
id: ejz-elementary-groups-explicit-kazhdan-constant-citation
kind: route
title: Import the explicit Kazhdan constant from the proof of Ershov--Jaikin-Zapirain's main theorem
target: ejz-elementary-groups-explicit-kazhdan-constant
requires: []
---

Citation route. Source: M. Ershov and A. Jaikin-Zapirain, *Property (T) for
noncommutative universal lattices*, arXiv:0809.4095v2 (21 Dec 2009), and Invent. Math.
179 (2010), 303--347, doi:10.1007/s00222-009-0218-2. The DOI, title, volume and pages
were checked through Crossref on 2026-09-13.

Read from the arXiv e-print TeX source `EL_n0909.tex` on MSI
(`/scratch.global/sauer354/fcah/src/EL_n0909.tex`, the file used by
`elementary-groups-over-fg-rings-property-t-citation`). The passages are in the section
"Property $(T)$ for $EL_n(R)$", subsection "Proof of Theorem~\ref{thm:main}".

- l.2364: "Throughout the section we fix an integer $n\geq 3$ and a finitely generated
  associative ring $R$ with $1$."
- l.2380--2385: "We fix a generating set $\{x_0,x_1,\ldots, x_d\}$ for $R$, where $x_0=1$.
  It is clear that the set \Sigma=\{e_{ij}(x_m)\, : \,i,j\in \{1,\ldots,n\}, i\neq j,\,\,
  0\leq m\leq d\} generates $EL_n(R)$."
- l.2443--2447: "Since $\Sigma$ is finite, we conclude that $EL_n(R)$ has property $(T)$,
  and moreover \kappa(EL_n(R),\Sigma)\geq \frac{1}{8(12\sqrt {2d}+2\sqrt {3n}+36\sqrt 2)}."
- l.2475--2477 (Theorem~\ref{Steinberg}): "The Steinberg group $St_n(R)$, $n\ge 3$, has
  property $(T)$. Furthermore, $$\kappa(St_n(R), \Sigma^{st})\geq \frac{1}{8(12\sqrt
  {2d}+2\sqrt {3n}+36\sqrt 2)}.$$"
- l.423 (introduction): "asymptotically this constant is $O(\frac{1}{\sqrt{n+d}})$ where $d$
  is the minimal number of generators of $R$".
- Definition of the Kazhdan constant, l.836--850 (subsection "Basic definitions"):
  - "$\kappa(G,S,V)$ is the infimum of the set $\{\epsilon> 0 : V \mbox{ contains an }
    (S,\epsilon)\mbox{-invariant vector.}\}$";
  - "$\kappa(G,S)$ ... is the infimum of the set $\{\kappa(G,S,V)\}$ where $V$ runs over
    $\Rep_0(G)$". Here $\Rep_0(G)$ is the set of representations without nonzero invariant vectors.

How the bound is proved: EJZ's A_2-system theorem gives `κ(EL_n(R), ∪ X_ij) >= 1/8` for the
block root subgroups. Kassabov's relative estimate (EJZ Proposition~\ref{Kassabov2}, "a
special case of [Ka2, Corollary 1.10]", i.e. Kassabov, Invent. Math. 170 (2007) 297--326)
gives the factor `12√(2d) + 2√(3n) + 36√2`.

The published version's equation numbering was not checked; cite the arXiv §6.1 proof of
the main theorem.
