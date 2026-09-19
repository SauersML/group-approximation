---
rg: 2
id: collins-haar-constant-matrices-asymptotic-freeness-citation
kind: route
title: Import Collins 2003, Theorems 3.1 and 3.5, on asymptotic freeness of Haar unitaries and constant matrices
target: collins-haar-constant-matrices-asymptotic-freeness
requires: []
---

**Source.** B. Collins, *Moments and cumulants of polynomial random variables on unitary groups, the
Itzykson--Zuber integral, and free probability*, Int. Math. Res. Not. 2003, no. 17, 953--982; arXiv:math-ph/0205010.
The arXiv PDF was fetched and its text extracted on 2026-09-17. Quotes are verbatim up to extraction artefacts (the
line breaks inside formulas are joined).

- **Theorem 3.1:** "Let U1, ..., Uk, ... be a collection of independent Haar distributed random matrices of Md(C)
  and (W^d_i)_{i∈I} be a set of constant matrices of Md(C) admitting a joint limit distribution for large d. Then the
  family ((U1, U1*), ..., (Uk, Uk*), ..., (Wi)) admits a limit distribution, and is asymptotically free."
- **Remark after Theorem 3.1:** "Note that this statement holds under the very weak hypothesis that the joint law
  of the family W admits a weak limit, i.e. it does not make any assumption of boundedness of the elements of W as
  d → ∞. In other words we do not have to consider asymptotic *-freeness, our method works in the framework of
  asymptotic algebraic freeness. [...] Besides, we do not have to restrict to diagonal elements or self adjoint
  elements for the (Wi)i as in the previous proofs."
- **Theorem 3.5:** "Let W be a family of matrices admitting a limit law and U1, ..., Uk be unitary independant random
  variables. Let w, u1, ..., uk be non-commutative random variables whose law is the limit joint law of
  W, U1, ..., Uk. If ε > 0, then one has P(|⟨W1 U^{ε1}_{i1} ··· Wn U^{εn}_{in}⟩ − ⟨w1 u^{ε1}_{i1} ··· wn
  u^{εn}_{in}⟩| ≥ ε) = O(d^{−2}) (3.3). In particular, the random variable ⟨W1 U^{ε1}_{i1} ··· Wn U^{εn}_{in}⟩
  converges in probability".
- **Introduction, summary of both theorems:** "(i) For any non-commutative polynomial Q in the variables W, U1, U1*,
  U2, U2* ..., d^{-1}Tr(Q(w_{i,d}, U1*, U2, U2* ...)) admits a finite limit in C. (ii) The family of sets of variables
  W, {U1, U1*}, ... is asymptotically free."

**Reading.**
- "Limit distribution" is the limit of `E tr` of noncommutative polynomials.
- `⟨.⟩` is the normalized trace `tr`.
- The `U_i` in Theorem 3.5 are the Haar unitaries of Theorem 3.1, the section's standing hypothesis.
- The target's (a) is Theorem 3.1, and its (b) is Theorem 3.5.
