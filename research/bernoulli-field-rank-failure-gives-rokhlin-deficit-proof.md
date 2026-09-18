---
rg: 2
id: bernoulli-field-rank-failure-gives-rokhlin-deficit-proof
kind: route
title: Evaluating Bernoulli variables at iid finite-field points turns a one-sided inverse pair into an equivariant code exact off a sparse defect set, whose site labels form a cheap generating partition
target: bernoulli-field-rank-failure-gives-rokhlin-deficit
requires:
  - seward-per-group-rokhlin-entropy-of-bernoulli-shifts
  - rational-function-field-crossed-products-have-the-rank-condition
  - virtually-hughes-free-field-crossed-products-are-stably-finite
artifacts:
  - research/artifacts/bernoulli-field-point-model-rokhlin-deficit-2026-09-17.md
---

All section and lemma numbers refer to the artifact.

1. **Finite coefficients** (Lemma 1). Choose a maximal ideal of a finitely generated coefficient ring with the
   denominators' leading coefficients inverted. The identity `AB = I_d` then reduces to `K_m(F_{q_0}) ⋊ G`, with
   nonzero denominators.
2. **Point model** (Section 2). On `Ω = (F_q^m)^G`, uniform, put `(π_ω(a u_g)ξ)(h) = a(h^{-1}ω) ξ(hg)`.
   - Covariance `σ_g(f)(ω) = f(g^{-1}ω)` gives equivariance (Lemma 2).
   - It also gives `π_ω(A)π_ω(B)ξ = ξ` at every `h` with `h^{-1}ω ∉ Z` (Lemma 3).
   - `μ(Z) <= C/q` by Schwartz–Zippel, which is Lemma 0 of the required rational-field proof (Lemma 4).
3. **Partition** (Section 3). The label `(ω(1), (π_ω(B)ξ)(1), ξ(1)·[1 ∈ D_ω])` generates `(F_q^{m+d})^G`
   (Lemma 5). Its entropy is at most `(m+r) log q + h_2(C/q) + (Cd/q) log q` (Lemma 6). For `q >= max(4, 4C, 2Cd)`
   this is below `(m+d) log q`.
4. **Conclusion.** Item 1 of the Seward import turns the deficit into `h_sup(G) < ∞`.
5. **Corollary** (Section 4). The shift is faithful, so the skew ring is simple, and the rank condition equals
   stable finiteness (item 1 of `virtually-hughes-free-field-crossed-products-are-stably-finite`). Stable
   finiteness passes to unital subrings, including `k[G]`.

**COMPLETE.**
