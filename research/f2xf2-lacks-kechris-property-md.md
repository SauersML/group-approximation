---
rg: 2
id: f2xf2-lacks-kechris-property-md
kind: claim
title: Some p.m.p. action of F2 x F2 is not weakly contained in finite actions
distinct_from:
  f2xf2-admits-nonsofic-action: that asks for a nonsofic action; an action outside the weak closure of finite actions may still be sofic, and stability in finite actions is exactly what would rule that out
  sl3z-cocompact-quotient-not-weakly-contained-in-finite-actions: that names one explicit SL3(Z) action and is open; this is an existence statement for F2 x F2, imported from the refutation of Connes embedding
  gohla-thom-lattices-no-weakly-bernoulli-liftable-action: that concerns actions lifted across a finite central kernel over p-adic lattices; this concerns plain actions of F2 x F2
artifacts:
  - research/artifacts/f2xf2-finite-action-stability-dichotomy-2026-09-16.md
---

`Γ = F_2 × F_2` has a p.m.p. action on a standard probability space that is not weakly contained in the
family of finite `Γ`-actions. In other words, `Γ` does not have Kechris's property MD.

*Trust surface: external.* There are two supports, both quoted verbatim in artifact §0.2–§0.3.

1. **Gohla--Thom** (arXiv:2403.09582v2, Remark 3.16) state it outright: "By the recent refutation of the
   Connes' Embedding Conjecture [23], there do exist p.m.p. actions of F2 × F2 that are not weakly contained
   in finite actions". No proof is written there.
2. **Fournier-Facio--Willett** (arXiv:2603.18456v2) give an independent chain:
   * `F_2 × F_2` is not RFD (Remark 5.23, via Ozawa and the negative solution of Connes embedding);
   * FD implies RFD (Definition 5.10);
   * property MD implies FD (page 68, attributed to Kechris).

The mechanism behind MD ⇒ FD is standard and recalled in artifact §4, not re-read in a primary source.
Koopman coefficients are polynomials in the statistics `μ(gA_i ∩ A_j)`, and the Gaussian action of a
realified representation contains that representation in its first chaos. So one may take the witness to
be the Gaussian action of a unitary representation of `Γ` that is not weakly contained in
finite-dimensional representations.
