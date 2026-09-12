---
rg: 2
id: uniform-gamma-iff-support-and-division-proof
kind: route
title: A central Lebesgue element cuts support projections under a; conversely support plus division lift to tracial almost divisibility
target: uniform-gamma-iff-tracial-support-projections-and-division
requires: []
artifacts:
  - research/artifacts/tw-invisible-gamma-support-gap-2026-09-12.md
---

Sections 1–2 of the artifact.

**Imports.** Each was read from the source PDF on 2026-09-12.
- CETW arXiv:1912.04207, Theorem 4.6: for separable nuclear algebras with no
  finite-dimensional quotients, CPoU, uniformly McDuff and uniform property
  Gamma are equivalent.
- Vaccaro arXiv:2604.24682v2, Definition 1.3 (tracial almost divisibility) and
  Proposition 1.6 (uniformly McDuff ⇒ tracially almost divisible; the converse
  under tracially locally finite nuclear dimension).
- Order zero lifting from `M_n`, as used in Vaccaro's proof.

**Lemma A.** TSP for `a` is equivalent to `γ_A(a) = 0`.
- Diagonal sequences of near projections in `closure(aAa)` define projections in
  `her(a)^U`.
- Clipped lifts of such projections are near projections.
- Both directions use that a maximizing trace at each index becomes a limit
  trace.

**(a) Uniform Gamma ⇒ TSP and PD.**
- *Setup.* Diagonal unital `M_N` in the relative commutant gives
  `σ(y e_ii) = σ(y)/N` for every tracial state `σ` and `y ∈ M_k(A)`.
- *The element.* Put `h = Σ t_i e_ii` with `t_i` equally spaced in `[η, 1]`, and
  `e = g_δ(a − h)`.
  - `e = a^{1/2} G(a,h) a^{1/2}` with `‖G‖ ≤ 1/η`, so `e ∈ her(a)^U`.
  - `σ(e − e²) ≤ k(δ/(1−η) + 1/N)`.
  - `σ(e) ≥ σ(a) − k(δ + η + 1/N)`.
- *Division.* Approximately central order zero maps chosen at each index
  against the entries of a given projection give a unital `M_n` commuting with
  it.

**(b) TSP and PD ⇒ uniform Gamma under tlfnd.**
- Take `p ∈ her(a)^U` with `σ(p) ≥ σ(a) − ε/2`, and divide it by PD.
- Lift the resulting order zero map into `closure(a M_k(A) a)`. This gives
  tracial almost divisibility of `a`.
- Conclude with Vaccaro's Proposition 1.6 and CETW Theorem 4.6.
