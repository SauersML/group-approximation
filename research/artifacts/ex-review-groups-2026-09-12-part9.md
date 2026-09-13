# EX review, groups: part 9. Uniform compression stability and vertex rounding

Lane `ex-verify-groups`, 2026-09-13, ~01:45 CDT. Index: `ex-review-groups-2026-09-12.md`.

These claims are reformulations that the non-hyperlinear and Q3.4 routes build on. None of them decides a
root: `non-hyperlinear-group`, `q3-4-resolved` and `binary-leavitt-unit-group-hyperlinear` compute open.

## 9.1 ex-free-unified-theory: `kazhdan-commutant-compression-stability-is-finitary` (4ca24765ad). PASS

- **Lemma (compressors suffice).** For `C = C_U(σ(Γ))`:
  - `σ(t) C σ(t)^-1 = C_U(σ(tΓt^-1)) ⊇ C`;
  - if `σ(t) C σ(t)^-1 <= C`, then equality holds and `σ(t)^-1` also normalizes;
  - `Γ` centralizes `C`;
  - so `σ(G) = <σ(F ∪ T)>` normalizes `C` iff every `t ∈ T` satisfies `σ(t) C σ(t)^-1 <= C`.
- **NORM ⇒ UCS.** Take counterexamples at `(1/k, k)`, with `s_k, t_k` fixed along the ultrafilter. The limit
  `σ` is a homomorphism and `z = [(z_k)]` centralizes `σ(Γ)`, but `σ(t) z σ(t)^-1` fails to commute with
  `σ(s)`.
- **UCS ⇒ NORM.** `η = max_s d(wσ(s), σ(s)w) > 0` for `w = σ(t)zσ(t)^-1 ∉ C`. Representatives form
  `(ε,R)`-models almost everywhere, and UCS at `η/2` bounds the limit by `η/2`.
- **Rows.** The sofic row follows from `sofic-groups-kill-rigid-compression-defects`. The weak MF row fails at
  the Theorem E pair through the MF amalgam `H_K`. The hyperlinear and linear sofic rows are open.

## 9.2 ex-free-unified-theory: `leavitt-unit-group-outside-class-iff-compression-stability` (0a5ab0a9fa, 1d83afbddd). PASS

- **(2 ⇔ 3).** This is 9.1 at the nine-leaf pair, `Γ = EL_α(R) <= EL_D(R) = R^x`, compressors `u, v`.
- **(2 ⇒ 1).** An injective `ρ`, together with the root defect `[u j u^-1, γ] != 1` for
  `j ∈ C_(R^x)(Γ)` (import), contradicts normalization.
- **(1 ⇒ 2).** A failure of normalization makes `σ` nontrivial. It is injective because `R^x` is simple, so
  `R^x ∈ C` by property (U) of the four classes.

Verdict PASS. At this pair nonhyperlinearity of `R^x` is exactly one uniform Hilbert–Schmidt centralizer
inequality, and `F_2`-linear soficity is exactly the rank version. It is a reformulation, not a decision.

## 9.3 ex-q34-kt-double: `kt-hyperlinear-coset-wreath-forces-nonroundable-vertex` (6447c33169, 218c71f3f9). PASS at the combining step

- **Model.** Amplification gives a trace-preserving embedding of a hyperlinear `W_K` into `U(∏_U M_n)`.
- **Moved lamp.**
  - `a_K ∈ R` because `K` fixes the coset `K`.
  - If `Γ` fixed every `gK`, then `Γ <= core_G(K)` and `N = <<Γ>> <= K`, which is excluded.
  - So some `γ gK != gK`. The lamps `a_(gK)` and `a_(γgK)` are distinct involutions whose product has trace
    `0`, so `||a_(γgK) - a_(gK)||_2 = √2`.
  - Hence `σ(G)` does not normalize `R`.
- **Contradiction under (H1).** (H1) would give `τ(1 - P_n) -> 0` through the four established premises
  (unit-type factorization, the root spectral mass bound, and the shallow and deep nonunit mass lemmas), and
  then normalization. Those premises were not re-derived here.

## 9.4 ex-q34-kt-double: `fournier-facio-vertex-rounding-fails-at-every-model` (4a45710df2). PASS

- **Genuine representations kill the simple factor.** `π(S)` is finitely generated, infinite and simple. So
  every homomorphism `π(S) -> U(n')` is trivial: it has finite image, since finitely generated linear groups
  are residually finite, and an infinite simple group has no nontrivial finite quotient.
- **Rounding transports this.** `||σ'_n(s) - π_n(s)||_2 <= Σ_j ||σ'_n(f_j) - π_n(f_j)||_2 -> 0` by unitary
  invariance, and the padding has weight `-> 0`. So `σ(s) = 1`.
- **Faithful models.** A trace-preserving model has `τ(σ(s)) = 0` for `s != 1`, so (H1) fails there.
- **Scope note, correct as recorded.** `hs-stable-vertex-rounding-for-every-model`, read over every
  infranormal Kazhdan pair, would already make the Fournier–Facio group non-hyperlinear. It is an open
  hypothesis, not a lemma.

## 9.5 Relay update for §3.2 and §8.1: `RF_fp` completeness novelty (1343d6b78d)

- **Novelty pass.** `ex-novelty` found no earlier Pi^0_2-hardness or completeness statement for `RF_fp` or
  `LEF_fp` within its bound (`research/artifacts/ex-novelty-rf-fp-pi02-pass-2026-09-13.md`).
- **Framing withdrawn.** The phrase "the residually finite Higman problem, open in the literature" is gone.
  The cell is framed by this repository, and KMS §1.1.7 print a different question, answered negatively
  by Rauzy (arXiv:2002.02540).
- **Credited precedents.** Rauzy arXiv:2111.01190v2 (`RF_fp` is not c.e.), Bridson–Wilton arXiv:1401.2273,
  and Rauzy arXiv:2605.30138 (boldface Pi^0_3 on marked groups).
- **Verdict unchanged.** The mathematical PASS for `e ↦ G_0(P(M_e))` stands. The relay wording should
  follow the corrected framing.
