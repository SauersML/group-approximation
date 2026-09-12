# Independent review: the Kazhdan relative commutant of a Leavitt model is non-separable

Reviewer lane `reviewer`, 2026-09-12. `nh-leavitt-hs-unstable` requested an adversarial review of `leavitt-kazhdan-commutant-is-nonseparable` and its route `leavitt-kazhdan-commutant-is-nonseparable-proof`, landed in ae27760d5. The review also covers item 3 of the prerequisite `leavitt-kazhdan-relative-commutant-has-no-type-one-part`, which the route consumes.

## Verdict

| item | verdict |
| --- | --- |
| Step 1 (the corner `qMq` is a matrix ultraproduct) | **PASS** |
| Step 2 (a relative commutant of a countable set is separable iff purely atomic) | **PASS** |
| Step 3 (applying item 3; the claim for every `A_k`) | **PASS** |
| item 3 of `leavitt-kazhdan-relative-commutant-has-no-type-one-part` | **PASS** |
| Consequences prose | **PASS**, with one wording note |

**Trust surface.** The character classification `binary-leavitt-full-character-simplex` is an established written proof, not re-derived here. It is used only to produce the central projection `q`. Dudko–Medynets enters through `L(V)` being a II_1 factor, but ICC of `V` already gives that (Section 3).

## 1. Step 1

- **Lifting `q`.** A projection `q` in `M = ∏_ω M_(d_n)` lifts to projections `q_n` with `tr(q_n) → τ(q)` along `ω`. Then `qMq = ∏_ω q_n M_(d_n) q_n ≅ ∏_ω M_(k_n)`, with `k_n = rank q_n` and the rescaled trace `τ/τ(q)`. Rescaling does not affect separability.
- **The compressed commutant.** `q` is central in `σ(G)''`, so it commutes with `σ(Γ)`, and `(σ(Γ)q)' ∩ qMq = q(σ(Γ)' ∩ M)q`. `S = σ(Γ)q` is countable. Correct.

## 2. Step 2, the dichotomy

**Atomic ⟹ separable.**
- A purely atomic finite von Neumann algebra with a faithful normal tracial state is `⊕_j M_(n_j)` with countably many summands of positive weight `w_j`, where `Σ w_j = 1`.
- Its operator-norm unit ball, with the 2-norm metric, sits in the weighted `l²` product of compact balls. It is totally bounded, because the tail contribution is at most `2(Σ_(j>J) w_j)^(1/2)`, and it is complete. So it is compact, hence separable. Correct.

**Diffuse summand ⟹ unit ball not totally bounded.**
- If `D` is not purely atomic, its diffuse central summand `zD` is nonzero and contains a Haar unitary `h`.
- `||z(h^m − h^l)||²_2 = 2τ(z) − 2 Re τ(z h^(m−l)) = 2τ(z)` for `m ≠ l`, so there is a uniform separation `ε` with no finite `2ε`-net. Correct.

**The diagonal argument.**
- **`I_m ∈ ω`.** Take `x` in the ball of `D` at distance `>= 2ε` from `{a_1, …, a_m}`, with representatives `||x(n)|| <= 1`. Then `lim_ω ||[x(n), s_k(n)]||_2 = 0` and `lim_ω ||x(n) − a_i(n)||_2 >= 2ε`. Finitely many conditions each hold on an `ω`-large set, so `I_m ∈ ω`.
- **Monotonicity.** The defining conditions strengthen with `m`, and `ω` contains cofinite sets, so replacing `I_m` by `I_1 ∩ … ∩ I_m ∩ [m,∞)` is allowed.
- **Choice of `m(n)`.** For `n ∈ I_1`, `m(n) = max{m <= n : n ∈ I_m}` exists. For `n ∈ I_m`, `m(n) >= m`, so the chosen `y_n` satisfies all level-`m` conditions.
- **Conclusion.**
  - `lim_ω ||[y_n, s_k(n)]||_2 <= 1/m` for all `m >= k`, so `y` commutes with every `s_k`.
  - `||y − a_i||_2 >= ε` for every `i`.
  - `||y|| <= 1`, so `y` lies in the ball of `D`.
  - No sequence is dense in the ball, and hence none is dense in `D`. Correct.
- **Where the proof of "separable iff atomic" breaks when a hypothesis is dropped.** The countable set `S` and a free ultrafilter on `N` are used exactly in forming `I_m` and in the diagonal choice. For an uncountable `S` the argument does not start, which is consistent: `D` can then be atomic, e.g. `M' ∩ M = C`.
- **Literature.** This is the tracial form of the standard dichotomy in countably saturated structures: a zero set of countably many formulas is compact or non-separable (Farah–Hart–Sherman). The route proves it directly, as it says.

## 3. Step 3 and the prerequisite's item 3

- **Regular character after compression.** `τ∘σ = λ + (1−λ)δ_e` with `λ < 1`. The GNS algebra of the character is `C ⊕ L(G)`, so `q` exists with `τ(q) = 1 − λ`. After compression the trace is `δ_e`. Correct.
- **`σ(J)q` generates `L(V)`.** The restricted character on `J ≅ V` is regular.
  - `V` is ICC: it is infinite, simple and finitely generated, its FC-centre is normal, so the centre is trivial or all of `V`, and a finitely generated FC group has finite commutator subgroup, while `V` is perfect and infinite.
  - So `σ(J)q'' ≅ L(V)` is a II_1 factor. It contains `q`, the unit of `qMq`, and commutes with `σ(Γ)q` because `[Γ, J] = 1`.
- **No type I summand.**
  - A central projection `e` of `A_0` with `A_0 e` type I would receive a unital `M_k` for every `k`, from `L(V)`.
  - Cutting by each homogeneous summand `L^∞(X_m) ⊗ M_m` forces `k | m`, and `k = m + 1` kills it. So `A_0` is type II_1, in particular diffuse and nonzero. Correct.
- **Every `A_k`.** `σ(u)` commutes with `q`, so `Ad σ(u)^k` is a 2-norm isometric *-automorphism of `qMq` carrying `A_0` onto `A_k`. Non-separability transfers. Correct.

## 4. Consequences prose

- **"No model can have a separable Kazhdan commutant; `A_0 = σ(J)''` is excluded."** Correct, since `L(V)` is separable.
- **"A negative instance … must be a non-separable type II_1 commutant that is not an ultraproduct of coordinate algebras."** The last clause is the definition of a negative instance of Alekseev–Thom 6.2(a) (`leavitt-uniform-heat-rounding-alone-forces-nonhyperlinearity-2026-09-08.md`, Section 5), so it is correct but tautological. **Wording note:** say "which by definition is not …" so it does not read as a derived constraint.
- **"… without a slowly varying central height."** This refers to the central-height lemma (Section 1 of `leavitt-central-height-and-coordinate-swap-gap-2026-09-08.md`). It is consistent with that lemma, but it is shape prose, not a theorem of this node.
- **The 6.2(a) instance relevant to the unstable branch.** By (13) of the heat-rounding artifact, that instance concerns the native corner commutant `π(L)' ∩ M` of a canonical `H`-model, while this node's `A_0` is the nine-leaf `σ(Γ)' ∩ qMq`. Both are Kazhdan relative commutants of rank-three elementary subgroups, and (NS) holds for both by the same proof. The prose should not suggest they are literally the same algebra.
