---
rg: 2
id: germ-complex-and-bux-gonzalez-morse-inputs-citation
kind: route
title: Import the germ complex from Belk–Hyde–Matucci and the Bux–Gonzalez criterion and Morse Lemma from Witzel–Zaremsky
target: germ-complex-and-bux-gonzalez-morse-inputs
requires: []
---

Citation import, read 2026-09-17 from the arXiv LaTeX sources.

## Belk–Hyde–Matucci

J. Belk, J. Hyde and F. Matucci, *Finite Germ Extensions*, arXiv:2407.03149 (v1). Source `main.tex`, SHA-256
`8fc0337eb0da9fd907c710b773e14bb4f3e7b005cf4564d0e5392e71b07a4afb`. Labels below are the LaTeX labels.

- **(FGE)** Introduction, before `thm:MainFinitenessTheorem`. "sing(h) = { p ∈ X | h does not agree with any element
  of B on any neighborhood of p }". The three conditions are quoted essentially verbatim:
  - "Every element of G has only finitely many singular points."
  - "G contains B, and indeed B is precisely the subgroup of G consisting of all elements that have no singular points."
  - "For every g∈G and p∈sing(g), there exists an h∈G with sing(h)={p} such that h agrees with g on some neighborhood of p."

  The composition rule is `rem:SingularPointsComposition`: "sing(kh) ⊆ h^{-1}sing(k) ∪ sing(h)".
- **(K)** Subsection `sec:GermComplex`, paragraphs "Germs", "B-germs", "Portraits" and "Partial portraits and the complex K".
  - "There is a natural left action of G on B-germs defined by g·(Bh)_p = (Bhg^{-1})_{g(p)}".
  - "(g·γ)(p) = g·γ(g^{-1}p)".
  - "let T_p be the tree whose vertices are the elements of Bgerm^*(G,p), with an edge from the basepoint (B)_p to the
    vertex *, as well as an edge from * to each nontrivial B-germ (Bg)_p".
  - "K be the (restricted) infinite product ∏_{p∈sing(G)} T_p".
  - The group of germs is "(G)_p = Stab_G(p)/RStab_G(p)" (Introduction, `subsec:IntroFinitenessProperties`).
  - The Morse function μ and the sublevel complex K_{≤n} are defined in the paragraph "The Morse function".
- **(Stab)** `prop:CellStabilizers`: "If C is any cube in K, then Stab_G(C) has a finite-index subgroup conjugate to
  SingFix_G(M,M') for some finite sets M⊆M' in sing(G), where |M'| is the maximum number of *'s in any vertex of C."
  `prop:FinitnessPropertiesFiniteIndex`: "If (B)_p has finite index in (G)_p for each point p∈M, then Fix_B(M') has
  finite index in SingFix_G(M,M')."
- **(Orb)** `prop:FinitelyManyOrbitsCells`. It gives the equivalence of "The induced action of B on sing(G)^n has
  finitely many orbits" with "The action of G on K_{≤n} has finitely many orbits of cubes".
- **(Conn)** `prop:nConnected`: "For n≥1, the sublevel complex K_{≤n} is (n−1)-connected."
- **(Fin)** `cor:MainFinitenessCorollary`, first alternative of its condition (3).
- **(RN)** `prop:BoundedAutomataGermExtension`: "each Röver–Nekrashevych group V_{d,r}G is a finite germ extension of
  the corresponding Higman–Thompson group V_{d,r}". The proof of `thm:RoverNek` verifies the hypotheses of
  `thm:MainFinitenessTheorem`, quoted:
  - "|(V_{d,r}G)_p:(V_{d,r})_p|<∞ for all p∈sing(V_{d,r}G)", via [BBMZ2, Proposition 5.5].
  - "the stabilizer in V_{d,r} of any finite set of rational points has type F_∞". This is Appendix A,
    `thm:Stabilizers`, which covers both Fix_{V_{d,r}}(S) and Stab_{V_{d,r}}(S).
  - "V_{d,r} acts with finitely many orbits on sing(V_{d,r}G)^n for all n≥1".

  The hypothesis (1) of `thm:MainFinitenessTheorem` that this verifies is "Stab_B(M) for every finite set
  M⊆sing(G)". So the stabilizer statement is applied to all finite subsets of the singular set.
- **Bounded automata group** (`sec:RoverNekrashevych`): "finitely generated and for each g∈G, there exist only finitely
  many infinite words i_1i_2i_3⋯∈X_d^ω for which all of the local actions f|_{i_1⋯i_n} are nontrivial." The
  introduction lists the Grigorchuk group, the Gupta–Sidki groups, the basilica group, BSV groups, finite state spinal
  groups and IMGs of postcritically finite polynomials.

## Witzel–Zaremsky

S. Witzel and M. C. B. Zaremsky, *The Σ-invariants of Thompson's group F via Morse theory*, arXiv:1501.06682 (v2).
Source `sigma_f_arxiv.tex`, SHA-256 `116db23896d9bb9d30a6fed4492ede864a5402be5b9c745064ba75c3200d3857`.

- **(BG)** `prop:bnsr_def`, credited "[bux04, Definition 8.1]" (K.-U. Bux and C. Gonzalez, *The Bestvina–Brady
  construction revisited*, J. London Math. Soc. 1999), together with `cor:changing_filtrations` ("Working definition").
  - The hypotheses are quoted: "Let G be of type F_m, acting cellularly on an (m−1)-connected CW complex Y. Suppose the
    stabilizer of any k-cell is of type F_{m−k}, and that the action of G on Y^{(m)} is cocompact."
  - The height function: "h_χ(gy)=χ(g)+h_χ(y)".
  - The conclusion: "[χ]∈Σ^m(G) if and only if the filtration (Y_{t≤χ})_{t∈R} is essentially (m−1)-connected", where
    "Y_{t≤χ} is defined to be the full subcomplex of Y supported on those vertices y with t≤χ(y)".
  - The text states: "It is a fact that this is independent of Y and h_χ." Witzel–Zaremsky apply it with Y an affine
    cell complex and h_χ affine on cells.
- **(ML)** `def:morse` and the Morse Lemma of Subsection `sec:morse`, quoted in the claim node. Also
  `obs:ascending_links_full`: "Ascending and descending links are full subcomplexes."
  - The ascending link of v is the link of v in the ascending star, the cells whose vertex of minimal refined height is v.
  - A k-connected pair (Y,Y_0) gives isomorphisms π_i(Y_0)→π_i(Y) for i<k and a surjection for i=k.
    Witzel–Zaremsky use exactly this in `obs:weak_bottleneck_trick`.
