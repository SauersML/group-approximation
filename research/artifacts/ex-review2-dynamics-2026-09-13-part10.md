# EX review 2, dynamics: part 10. Exact and approximate central Bernoulli lifts; conditional wave-2 routes

Lane `ex-verify2-dynamics`, wave 2.
- **Lanes.** ex2-rokhlin-almost-cocycle (633cd9d32a, 8ed72cc152, 336e7e5f3a), ex2-bernoulli-exactification (69c0ded2e5)
  and ex2-hecke-pair-positive (8bff272fae).
- **Artifact.** `weakly-bernoulli-lifts-degree-one-reduction-2026-09-13.md`, §§13–14, read in full.

| node | status | verdict |
|---|---|---|
| `central-bernoulli-lifts-force-splitting` (+ `-proof`; artifact §13, Theorem R0) | established | PASS |
| `degree-one-bernoulli-expansion-excludes-weak-lifts` (+ `-proof`; artifact §14, Theorem R1) | established | PASS (conditional on expansion, as stated) |
| route `deligne-weak-lift-obstruction-from-congruence-cosystole` | unfired | valid implication; premise `deligne-class-congruence-cosystole-bounded-below` OPEN |
| routes `function-field-rank-one-vertex-action-from-rank-two`, `function-field-rank-one-vertex-action-via-separable-approximants` | unfired | valid implications (§10.3); target OPEN |
| status edits at 69c0ded2e5 and 336e7e5f3a | OPEN claims | consistent with part 9 |

## 10.1 Theorem R0: PASS

- **Two copies.** `δb = α_0`, and `α_0` is constant, so `d = b∘p_1 − b∘p_2` has `δd = 0`: an honest `A`-valued cocycle of
  the diffuse Bernoulli shift `X^2`.
- **Popa.** Theorem 0.1 (verbatim, part 3): `A` is finite, hence of finite type, and `X^2` is s-malleable. So
  `d = δf + χ`.
- **Three copies.** `d_12 + d_23 − d_13 = 0` gives `δF + χ = 0` for `F = f_12 + f_23 − f_13`.
- **Kill `χ`.** `F` is `ker χ`-invariant, and finite-index subgroups act ergodically on Bernoulli shifts of infinite
  groups. So `F` is constant and `χ = 0`.
- **Separate variables.** For a.e. `y`, `f(x,x') = f(x,y) − f(x',y) + c`.
- **Constant cochain.** Then `(b − δg)(x) = (b − δg)(x')` a.e., so `b − δg = a` is a constant cochain, and
  `α_0 = δa`. So `α = 0` in cellular cohomology with constant coefficients.

## 10.2 Theorem R1: PASS

- **Steps 1–3.**
  - `|δd| <= 2ε`, and expansion gives `z` with `|d − z| <= ρ(2ε) = ε_1`.
  - Popa gives `z = δf + χ`.
  - Telescoping on three copies gives `µ(F∘s^(−1) − F + χ(s) != 0) <= 3ε_1`.
- **Step 4 (spectral gap).**
  - For each character `ψ`, `Φ = ψ∘F` has `||π(s)Φ − θ(s)Φ||_2 <= 2√(3ε_1)`, with `θ = ψ∘(−χ)`.
  - The constant and `L^2_0` parts are orthogonal, and both parts satisfy the bound. `L^2_0` of a Bernoulli shift is a
    multiple of `ℓ^2(Γ)`, twisting by a character does not change that, and `Γ` is nonamenable (w-rigid). So `Φ_0` is
    `O(√ε_1)`, and `|1 − θ(s)|` is `O(√ε_1)`.
  - Nontrivial `|A|`-th roots of unity are uniformly far from 1, so `χ = 0`. Fourier inversion gives `F = c` off `C_3ε_1`.
- **Steps 5–7.**
  - Fubini picks `y`.
  - `h_s = b_s − (g∘s^(−1) − g)` has `h_s(x) = h_s(x')` off `ε_1 + 2ε_2`.
  - `Σ_a µ(h_s = a)^2 = P(h_s(x) = h_s(x'))` gives `µ(h_s != a_s) <= ε_3`.
- **Step 8.** `δh = δb` exactly, so `δa = α_0` off `ε + ℓε_3`. Both sides are constants, so `α = 0` below threshold.
- **Scope.** The input "degree-one cocycle expansion of `[0,1]^Γ`" is open for `Sp_4(Z)`
  (`bernoulli-shifts-have-degree-one-cocycle-expansion`, OPEN), and nothing fires into
  `deligne-triple-cover-no-weakly-bernoulli-liftable-action`.

## 10.3 Conditional routes

- **`deligne-weak-lift-obstruction-from-congruence-cosystole`.**
  - Restriction to `Γ(3)` preserves liftability and weak containment.
  - `Bern ≺ Γ^ ≺` finite actions, by Abért–Weiss and the ultraproduct embedding (as in part 7 §7.4).
  - The Gohla–Thom chain with Shapiro's isometry bounds the norm below by the congruence cosystole.
  - Item 4 of `bernoulli-maximizes-extension-class-norm` concludes. The premise is OPEN.
- **`function-field-rank-one-vertex-action-from-rank-two`.**
  - `diag(g,1)` has entries in `F_2[t]` iff `g` does, so `L1 ∩ C = C1`.
  - GKP Proposition 2.15(3) (restriction) and 2.15(2) (orbits) give soficity of `L1 ↷ L1/C1` from the rank-two action.
  - The premise `function-field-building-vertex-action-is-sofic` is not established.
- **`function-field-rank-one-vertex-action-via-separable-approximants`.**
  - *Amalgam.* `L1 = C1 *_(B0) C1'`: Serre's tree theorem, density and edge-transitivity.
  - *Generators.* `B0 = <V, V'>`, by the stated Euclidean reduction: `deg a` drops every two steps, and `a(0) = 1` is
    preserved.
  - *Directed system.* The truncations `Γ_n = C1 *_(B0,n) C1'` form exactly the data of item 3 of
    `sofic-coset-actions-pass-to-marked-colimits` (PASS, part 9).
  - *Missing input.* Separability of the vertex group in every truncation, `sl2-laurent-f2-amalgam-approximants-separate-the-vertex`,
    which is OPEN. Only degree one is proved (part 9 §9.5).

## 10.4 Status edits

- **69c0ded2e5.** It adds "Status" paragraphs to the i.i.d. density, DENSE, ARI and collapse claims: each holds iff
  `every-group-has-positive-rokhlin-entropy-action`. This matches item 7 of the spectral-gap node (part 9 §9.2). None
  of those claims is marked refuted, which is correct, since the equivalence goes through an open question.
- **336e7e5f3a.** It records the exact case R0 and the degree-one reduction R1 on
  `weakly-bernoulli-liftable-actions-force-virtual-splitting` (OPEN). It is consistent with §§10.1–10.2.
