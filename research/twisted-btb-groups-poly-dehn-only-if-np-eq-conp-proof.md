---
rg: 2
id: twisted-btb-groups-poly-dehn-only-if-np-eq-conp-proof
kind: route
title: Twisted Brin-Thompson groups contain 2V, and 2V has no polynomial-Dehn finitely presented overgroup unless NP = coNP
target: twisted-btb-groups-poly-dehn-only-if-np-eq-conp
requires: []
---

All three imports were read in the arXiv TeX sources on MSI on 2026-09-13; see
`research/artifacts/simple-bors-2026-09-13.md` for the surrounding lines.

1. **Containment.** Belk--Zaremsky, *Twisted Brin--Thompson groups*,
   arXiv:2001.04579, TeX l.155, verbatim: "When $S$ is infinite, the group
   $\SVG$ is ``large'' in the sense that it contains $sV$ for all~$s\in \N$."
   So `2V <= SV_G`.

2. **Birget's theorem and remark.** Birget, *The word problem of the
   Brin--Thompson group is coNP-complete*, arXiv:1902.03852.
   - Abstract, TeX l.42: the word problem of `nV` "over a finite generating
     set is {\sf coNP}-complete for every $n \ge 2$".
   - Completeness is under polynomial-time many-one reductions for `2V`, and
     under bounded-arity conjunctive reductions for the general `n` (TeX
     l.2887, l.2905).
   - TeX l.91--94, verbatim: "The Theorem implies that if ${\sf NP} \ne
     {\sf coNP}$ then the Dehn function of $nV$ (for $n \ge 2$) has no
     polynomial upper bound; more strongly, $nV$ cannot be embedded into a
     finitely presented group with polynomially bounded Dehn function (by
     \cite{SBR, BORS})."

3. **Why the remark holds.** Birget--Ol'shanskii--Rips--Sapir, arXiv:math/9811106,
   TeX l.228, verbatim: "if a finitely generated group $G$ is a subgroup of a
   finitely presented group with polynomial isoperimetric function then the
   word problem in $G$ is in NP". So a polynomial-Dehn overgroup of `2V` puts a
   coNP-complete problem in NP. Every coNP problem then reduces in polynomial
   time to a problem in NP, so `coNP <= NP`. Taking complements gives
   `NP = coNP`.

4. **Conclusion.** `SV_G` is finitely presented by hypothesis and contains `2V`
   by step 1. If its Dehn function were polynomially bounded, step 2 would
   force `NP = coNP`. `∎`
