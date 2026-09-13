---
rg: 2
id: stage-models-cannot-close-the-leavitt-hexagon-proof
kind: route
title: Łoś through a finitely presented group with no finite quotients, per-stage colimits, and nonsoficity through the Hamming comparison
target: stage-models-cannot-close-the-leavitt-hexagon
requires:
  - leavitt-unit-groups-have-no-unstable-k2-at-rank-three
  - steinberg-group-is-glued-over-the-permutohedron
  - graphs-of-locally-finite-groups-carry-regular-rank-models
  - leavitt-unit-group-finitely-presented
  - binary-leavitt-unit-group-is-simple
  - prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre
  - openai-leavitt-unit-nonsofic
  - d-ary-leavitt-groups-nonsofic-over-finite-fields
  - projective-leavitt-unit-groups-mod-scalars-are-nonsofic
  - monomial-rank-models-are-hamming-models
artifacts:
  - research/artifacts/hexagon-closing-letter-stage-obstruction-2026-09-12.md
  - research/artifacts/gk-vf-gate-verification-2026-09-12.md
---

Complete proof: artifact Sections 1–5.
* Section 1: Proposition 1.1.
* Section 2: Lemmas 2.1–2.2, Theorem 2.3, Corollary 2.4.
* Section 3: Proposition 3.1, Corollary 3.2.
* Section 4: calibrations.
* Section 5: the ternary transfer.

- **The letter.** The hexagon has one non-forest edge `e_6 : 132 -> 123`, with `K = <x_12(R), x_13(R)>`.
  - `t` maps to a generator of `π_1(graph) = Z`, and killing it identifies the two lifts of `K`.
  - The quotient is `colim U_π = G`, by (SPG2) and `K_2(3,R) = 0`.
  - In the Theorem 1.1 model, the letter permutations form a coset `π_n^0 Z_n` with `Z_n ≅ K_n wr Sym(r_n)`.
- **No exact closing.** `G` is finitely presented. It has no nontrivial finite quotient and no nontrivial
  homomorphism into `GL_m` of a commutative ring:
  - binary, because `G` is simple and infinite;
  - ternary, because `G` is perfect and `G/Z` is simple;
  - for linear targets, by Malcev.

  By Łoś, a homomorphism into an algebraic ultraproduct of such groups factors stagewise. If it also kills `t`, it
  factors through `G`, so it is trivial. Per stage, the finitely many relators of `G` and `x_12(1) = w` hold in the
  six-piece colimit `C_n` for `n >= n_1`. So every finite quotient of `C_n` kills `x_12(1)`, and `id ∉ π_n^0 Z_n`.
- **No rank-null closing.** Suppose `rk(σ(t) - 1) = 0`.
  - Then `σ` descends to `G -> prod_U Sym / null`, and the Hamming comparison keeps `x_12(1)` nontrivial.
  - The kernel is `1` in the binary case and lies in `Z` in the ternary case.
  - So `G` or `G/Z` would be sofic by Elek–Szabó, contradicting nonsoficity.

  The uniform `ε_p` over Theorem 1.1 models comes from a diagonal over models, using `rank(π - I) >= |supp π|/2`
  and relator error `4L/k`.
- **Ternary.** Every step is field-independent. The root-pair pieces have order at most 27 and exponent 3.

*Verified independently by `w4-vf-gate` (2026-09-12), Section 38 of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS.*
