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
- **Orthogonal to constants is not enough (2026-09-13, un-reduced-cstar).**
  - Inside ℓ²_0(F_k), the permutation module on unimodular columns of the ring models contains a vector exactly
    invariant under σ_k of a non-amenable stabilizer of e_1. That stabilizer is EL_{n−1}(R_X), which is Kazhdan
    for n ≥ 4.
  - So λ^0_{F_k}∘σ_k, and any representation containing that module, still has norm-1 outliers
    (`ring-model-permutation-vectors-block-strong-convergence`).
- **Genuine representations are excluded (2026-09-13, un-reduced-cstar).** EL_n(R_X), for X infinite minimal,
  has no nontrivial finite quotient, hence no nontrivial finite-dimensional unitary representation, so it is not
  PMF (`minimally-almost-periodic-groups-are-not-pmf`). An MF embedding must use asymptotic representations far
  from genuine ones.
- **What any MF model must satisfy (2026-09-13, un-reduced-cstar; artifact
  `research/artifacts/un-reduced-cstar-2026-09-13-part1.md` §2.2–2.4).**
  - The lower bound liminf ‖V_k(z)‖ ≥ ‖λ(z)‖ is automatic once normalized traces converge to τ.
  - Along ω the traces do converge to τ for every MF embedding, once the amenable radical is trivial (BKKO
    Thm 4.1, `bkko-reduced-traces-concentrate-on-amenable-radical`).
  - What is missing is exactly a deterministic no-outlier upper bound for models with no almost invariant vectors
    under non-amenable subgroups, e.g. cuspidal-type irreducibles of the finite models (heuristic). The paradox-side
    counterpart is decided: `measure-free-steinberg-el-n-reduced-cstar-not-mf`.
