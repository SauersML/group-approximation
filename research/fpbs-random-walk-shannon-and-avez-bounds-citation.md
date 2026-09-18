---
rg: 2
id: fpbs-random-walk-shannon-and-avez-bounds-citation
kind: route
title: Import the Avez entropy bound and pathwise entropy limit from Lyons–Peres
target: fpbs-random-walk-shannon-and-avez-bounds
requires:
  - kesten-amenable-stabilizer-uniform-gap
---

Citation import, not a reproof. Source: R. Lyons and Y. Peres, *Probability on
Trees and Networks*, Chapter 14. The quotes come from the PDF version dated 19
August 2026. In the text extraction the minus signs are lost, so they are
restored below.

- Section 14.1, (14.3): the limit "h := lim_{n→∞} H(Xn)/n exists" for
  transitive chains with `H(X_1) < ∞`, and it is called the Avez entropy.
- Proposition 14.6 (book page 474): "For any symmetric Markov chain
  (p(x,y) = p(y,x) for all x,y) and any initial state o, we have
  lim inf_{n→∞} H(Xn)/n ≥ 2 log(1/ρ). In particular, transitive symmetric
  chains with ρ < 1 have h > 0."
- Theorem 14.10 (Pathwise Limits, book page 476): "Let ⟨Xn⟩ be a transitive
  Markov chain starting at o. (i) If the chain is endowed with an invariant
  graph metric d and E d(o,X1) < ∞, then almost surely
  lim_n (1/n) d(o,Xn) = l. (ii) If H(X1) < ∞, then almost surely
  lim_n −(1/n) log p_n(o,Xn) = h."
- Notes to Chapter 14: "Theorem 14.10(ii) is due to Vershik and Kaimanovich
  (1979, 1983), Derriennic (1980), and Kaimanovich and Woess (2002)."

In LP, `ρ` is the spectral radius `limsup p_n(o,o)^{1/n}` of the chain
(Section 6.2). For a random walk `p(x,y) = mu(x^{-1}y)`, a symmetric `mu`
makes the chain symmetric, and left translation makes it transitive. Almost
sure convergence implies convergence in probability, which gives item 2 of the
target. Item 3 is the one-line inequality stated there, together with the
Kesten fact quoted verbatim in `kesten-amenable-stabilizer-uniform-gap`:
"rho = rho(A,S) = || (1/|S|) sum over s in S of lambda_A(s) || < 1 ... which is
< 1 exactly when A is nonamenable."

Read from the PDF on 2026-09-17. This route asserts only that the cited
theorems say what the target records.
