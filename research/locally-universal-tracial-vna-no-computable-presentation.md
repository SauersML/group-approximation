---
rg: 2
id: locally-universal-tracial-vna-no-computable-presentation
kind: claim
title: No locally universal tracial von Neumann algebra admits a computable presentation (Arulseelan--Manzoor, conditional on MIPco = coRE)
distinct_from:
  free-direct-product-max-tensor-presentation-is-not-computable: that is Goldbring--Sinclair's obstruction for maximal tensor products of qc-full C-star algebras; this is Arulseelan--Manzoor's obstruction for locally universal tracial von Neumann algebras.
---

**Literature import (Arulseelan--Manzoor, arXiv:2508.21709).**  Theorem
`SNoCompPres` (`applications.tex` l.47--49), verbatim: "No locally universal
tracial von Neumann algebra admits a computable presentation."

**Definitions, verbatim from the same source.**
- Locally universal (`applications.tex` l.10): "every separable tracial von
  Neumann algebra embeds in an ultrapower of $\mathcal{S}$."
- Presentation and computable presentation (`prelims.tex` l.36--45): a
  presentation is a pair `(N, (a_n))` whose special points `a_n` generate a
  *-algebra that is `||.||_2`-dense in `N`; rational points are *-polynomials
  with coefficients in `Q(i)` in special points; the presentation is computable
  if there is an algorithm which, on input a rational point `p` and `k`, returns
  a rational `q` with `| ||p||_2 - q | < 2^(-k)`.

**Conditionality.**  The theorem rests on their Theorem `MIPcoEncoding`, whose
displayed statement in the introduction begins "Suppose $\MIPco=\coRE$"
(`intro.tex` l.9--16).  The equality `MIPco = coRE` is Lin's announced result
(their citation `lin_mipco_2025`), which is a preprint.  The proof of
`SNoCompPres` also uses Goldbring--Hart, *The universal theory of the
hyperfinite II_1 factor is not computable*, Bull. Symb. Logic 30 (2024),
Proposition 2.7, as cited at `applications.tex` l.51.  Neither Lin's preprint
nor the Goldbring--Hart proposition was re-read here.
