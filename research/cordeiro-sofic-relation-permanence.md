---
rg: 2
id: cordeiro-sofic-relation-permanence
kind: claim
title: Sofic p.m.p. equivalence relations pass to restrictions, invariant partitions, finite-index overrelations and products
distinct_from:
  paunescu-sofic-action-class-permanence: that imports Paunescu's permanence for groups all of whose actions are sofic; this imports Cordeiro's permanence for sofic equivalence relations themselves
artifacts:
  - research/artifacts/paunescu-class-measure-equivalence-2026-09-12.md
---

**ESTABLISHED (literature import).** L. Cordeiro, *An elementary approach to
sofic equivalence relations*, arXiv:1608.05608v2 (13 Oct 2016), read from the
PDF, pages 3 to 8 (transcriptions in the artifact).

Let `R` be a countable Borel p.m.p. equivalence relation on a standard
probability space `(X, μ)`, with measured full semigroup `[[R]]` and trace
`tr φ = μ{x ∈ dom φ : φ(x) = x}`.

* **Definition 2.1** (Ozawa). `R` is sofic if for every finite `K ⊆ [[R]]` and
  `ε > 0` there are `N` and `π : [[R]] → [[N]]` into the partial bijections of
  `[N]` that are `ε`-multiplicative on `K` and match traces on `K` up to `ε`.
* **Theorem 2.2.** `R` is sofic iff `[[R]]` embeds isometrically in a metric
  ultraproduct `Π_𝒰 [[n_k]]`, iff such an embedding preserves the trace.
* **Remark after 2.2.** An increasing union of sofic relations is sofic.
* **Proposition 3.2(a).** *"If R is sofic and A ⊆ X is any (non-null) subset,
  then R|A is sofic."* (b) For a countable Borel partition of `X` into non-null
  `R`-invariant sets, `R` is sofic iff each restriction is.
* **Theorem 3.4.** If `R ⊆ S` has finite index and admits invertible choice
  functions (for example when `R` is ergodic), and `R` is sofic, then `S` is sofic.
* **Corollary 3.5.** Every hyperfinite relation is sofic.
* **Theorem 3.6.** `(X,μ,R)` and `(Y,ν,S)` are sofic iff `(X×Y, μ×ν, R×S)` is.

Cordeiro's remark after Proposition 2.4 says this description is equivalent to a
sofic embedding of `vN(R)` in the sense of Păunescu (his reference [11], J. Funct.
Anal. 261 (2011)), which Păunescu shows agrees with Elek--Lippner's definition.
Section 1 of the artifact checks the equivalence with Păunescu's Definition 1.13
directly. So Păunescu's Proposition 1.15 (`paunescu-sofic-action-class-permanence`)
can be combined with the results above.

**Trust surface.** Refereed status not checked. Statement-level import. The
proofs of 3.2(a) and 3.6 were read and are short and elementary.
