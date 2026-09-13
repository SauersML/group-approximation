---
rg: 2
id: directly-finite-subshift-el-n-reduced-cstar-is-mf
kind: claim
title: "For a directly finite subshift ring, is the reduced C*-algebra of EL_n MF?"
distinct_from:
  subshift-elementary-mf-iff-word-edges-lie-on-cycles: that decides operator MF of the group itself; this asks for MF of the reduced group C*-algebra, which needs strong convergence of models.
artifacts:
  - research/artifacts/un-traces-2026-09-13-part1.md
---

**OPEN.** Let X be a finite-alphabet subshift with R_X = LC(X,F_q)⋊Z directly finite, and n ≥ 4 (e.g. X
infinite minimal). Is C*_r(EL_n(R_X)) an MF algebra, i.e. does it embed in a norm matrix corona?

**Context.**
- **Paradox side.** For a full complementary idempotent, C*_r(EL_n(R)) is separable, stably finite and not
  MF (`non_mf_groups_exist.tex` Cor l.1038).
- **Traces fail.** For infinite Kazhdan G the canonical trace on C*_r(G) is never amenable. Apply Ozawa
  Thm 6.1(i) to C*_r(G) ⊆ B(ℓ²G); an A-central state restricts to an invariant mean on ℓ^∞(G).
- **Not QD.** C*_r(G) is never QD (Rosenberg, recalled). So MF is the only matricial property of the reduced
  algebra left to decide.
- **What a positive answer gives.** An embedding gives G operator MF (manuscript Lemma
  `prop:mf-residual-calculus`) with norms reproducing the reduced norm, i.e. GKMP-type MF.

## Attempts

- **Regular representations of LEF models (2026-09-13, un-traces).** They never converge strongly to λ_G.
  For a finite symmetric generating set S, ‖Σ_{s∈S} λ_{F_k}(σ_k(s))‖ = |S| from the constant vector, while
  ‖λ_G(Σ_s u_s)‖ < |S| for non-amenable G (Kesten). Any strong-convergence approach must use pieces
  orthogonal to invariant-like vectors. Property (T) supplies no uniform spectral gap there, because the
  finite models are not representations.
