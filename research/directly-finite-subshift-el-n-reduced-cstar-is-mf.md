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
  `prop:mf-residual-calculus`) with norms reproducing the reduced norm, i.e. clauses (1) and (3) of GKMP-type MF, not the trace clause (2) (review 2026-09-13).

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

- **Every representation of the ring models is excluded (2026-09-13, sk-cstar-mf, unreviewed).**
  - On an embedded Laurent lattice SL_4(F_q[u_V^{±1}]) (a tower of height 2 plus the first-return unit), the
    models are genuine congruence representations through SL_4(A_ℓ), with A_ℓ a finite principal ideal ring
    (`lef-models-are-congruence-representations-on-laurent-lattices`).
  - The Magee–de la Salle argument works verbatim over such rings: every representation of SL_4(A_ℓ) has a
    nonzero SL_2(A_ℓ)-invariant vector (`sl4-over-finite-chain-rings-has-sl2-invariant-vectors`).
  - So for ANY unitary representations ρ_ℓ of the finite models (cuspidal, Steinberg or otherwise), ρ_ℓ∘φ_ℓ
    has the norm-4 outlier z = S+S^{-1}+T+T^{-1} for a free pair in SL_2(F_q[u]) and never converges
    strongly (`periodic-word-model-representations-never-converge-strongly`). The same holds for every exactly
    matricial window model.
  - The cuspidal-type heuristic above is dead. An MF embedding of C*_r(EL_n(R_X)) needs asymptotic
    representations that are not genuine on any embedded SL_4(F_q[t^{±1}]).
- **Dichotomy with stability of the Laurent lattice (2026-09-13, sk-matricial-stability, unreviewed).**
  - Every finite-dimensional unitary representation of `SL_n(F_q[t^{±1}])`, `n ≥ 4`, is congruence and fixes a
    block-`SL_2` vector. The proof uses torsion root subgroups, a level ideal and Bass–Milnor–Serre Corollary 4.3, with
    no superrigidity (`laurent-sl-n-representations-have-sl2-invariant-vectors`).
  - `R_X ⊇ F_q[u^{±1}]`, so `EL_n(R_X) ⊇ SL_4(F_q[t^{±1}])`. An MF embedding of `C*_r(EL_n(R_X))` therefore forces
    `SL_4(F_q[t^{±1}])` to be NOT point-norm matricially stable
    (`laurent-sl4-stability-makes-overgroups-reduced-non-mf`).
  - Conversely, stability of that lattice decides this claim negatively. The crux is the open
    `laurent-sl4-matricially-stable`, and the negative root at the note's group is
    `subshift-elementary-group-reduced-cstar-is-not-mf`.

**Review (un-verify-measure, 2026-09-13): display checked (OPEN node).** The GKMP clause is corrected. See `research/artifacts/un-review-measure-2026-09-13-part2.md` §T6.
