---
rg: 2
id: hoffman-weintraub-level-four-siegel-betti-numbers-citation
kind: route
title: Import Hoffman--Weintraub Theorem 1.2 on the Betti numbers of Gamma_2(4)
target: hoffman-weintraub-level-four-siegel-betti-numbers
requires: []
---

Citation import. On 2026-09-17 the PDF
`https://www.math.lsu.edu/~hoffman/papers/level4.pdf` was fetched and its text
extracted. J. William Hoffman and Steven H. Weintraub, *Cohomology of the
Siegel modular group of degree two and level four*. The abstract reads: "We
compute the cohomology of the subgroup of the integral symplectic group of
degree 2 consisting of matrices ≡ 1 mod 4. This is done by computing the
cohomology of the moduli space of principally polarized abelian surfaces with
a level 4 structure."

Verbatim.

- **p. 2, Theorem 1.2.** "The Betti numbers h_i = dim H^i(Γ(4); Q) of the
  principal congruence subgroup of level 4 in Sp4(Z) are 1, 0, 118, 1112, 481
  for i = 0, ..., 4 and 0 for all other values."
- **p. 2--3, following Theorem 1.2.** "Notice that the Euler characteristic is
  −512 which is the predicted value from the formula of Siegel:" (the displayed
  formula that follows was garbled by text extraction; its legible tokens are
  "−512 = ", "[Γ(1) : Γ(4)]", "1440" and "737280", consistent with
  `zeta(-1) zeta(-3) = -1/1440` and index `737280`).
- **p. 2, Theorem 1.1 (quoting Lee--Weintraub [18] for the compactification).**
  "The Hodge numbers h^{p,q} = dim_C H^{p,q}(A2(4)*) are ... h^{1,1} = h^{2,2}
  = 226".

Here `Γ(4)` is the principal congruence subgroup `ker(Sp_4(Z) -> Sp_4(Z/4))`,
as in the abstract. Used at statement level; only `h_2 = 118` is used downstream.
The proof, via the Leray spectral sequence of the Igusa compactification and
the Lee--Weintraub computation of its cohomology, is not re-derived here.
