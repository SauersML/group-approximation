# sk-verify-20 part 1: Theorem P, weakly dense Popa combs in every separable II_1 factor (2026-09-14)

Lane sk-verify-20. Priority item from main, queue line 27: `separable-ii1-factors-have-weakly-dense-popa-combs` (sk-popa-input2, c32e108f15), artifact `research/artifacts/sk-popa-input2-2026-09-14-part1.md`. Main tip at review: 53a33bef9c. No review line was on the node before this. Every step below was re-derived by hand, adversarially. Sources were re-read on MSI (`/scratch.global/sauer354/sk/sk-popa-lgx/{math_0111286,math_0207005,math_0304009}/src`).

## Verdict
**PASS-WITH-FIXES.** Theorem P is correct: every II_1 factor with separable predual contains a weakly dense unital C*-subalgebra with a comb, hence a weakly dense Popa algebra. Fixes F1–F4 (§3) concern the schedule, scope, locator and novelty wording. No GAP, no FAIL.

## 1. The lemmas, re-derived
- **Setup.**
  - `R_{k,m}` (`m ≥ k`) and `g_k` are commuting projections in distinct tensor factors, and `g_k + Σ_{m≥k}R_{k,m} = 1` (first tooth at or after `k`, or none).
  - `τ(g_k) = ∏_{i'≥k}(1−1/r_{i'}) > 0` and `τ(1−g_k) ≤ Σ_{i'≥k}1/r_{i'}`.
  - `z_k` is a strongly convergent sum of partial isometries with orthogonal supports summing to 1, so it is unitary.
- **Lemma 1.** For `j ≥ k`:
  - `g_k ≤ 1−p_j` kills `u_k`;
  - `R_{k,m} ≤ 1−p_j` for `m > j`, and `R_{k,j} ≤ p_j`;
  - for `m < j`, `c_k^{(m)} ∈ ⊗_{i'≤m}N_{i'}` commutes with `N_j`.
- **Lemma 2 (C1).**
  - `z_kp_j = Σ_{k≤m≤j}c_k^{(m)}p_j`.
  - For `m = j`: `c_k^{(j)} ∈ p_j(⊗_{i'≤j}N_{i'})p_j = (⊗_{i'<j}N_{i'})⊗ℂp_j`, since `p_j` is rank one in `N_j`.
  - So `A_je_j = (⊗_{i'<j}N_{i'})p_j ≅ M_{D_j}`, with unit `e_j`.
- **Lemma 3 (C3).** `Σ_lf_{l1}f_{11}f_{1l} = Σ_lf_{ll} = 1`, with `f_{l1} ∈ N_i ⊆ A_{i+1}`.
- **Lemma 4 (weak density).**
  - Polar part `u_k` with `x_k = u_k|x_k|`: a finite von Neumann algebra, so the partial isometry extends to a unitary.
  - `g_k − x_k^*x_k = ((1−g_k)y'_kg_k)^*((1−g_k)y'_kg_k)`, so `τ(g_k − x_k^*x_k) ≤ τ(1−g_k)`.
  - `(1−t)² ≤ 1−t²` on `[0,1]` gives `‖u_k − x_k‖_2 = ‖g_k−|x_k|‖_2 ≤ τ(1−g_k)^{1/2}`.
  - The identity `z_k − y'_k = (u_k−x_k) − (1−g_k)y'_kg_k + (z_k−y'_k)(1−g_k)` holds, using `z_kg_k = u_k`. With `‖ab‖_2 ≤ ‖a‖‖b‖_2` this gives `1+1+2 = 4`.
  - Bounded 2-norm convergence gives strong convergence in `L²(M)`, so `A'' = M`.
- **§3 splitting.**
  - `1−b_k = Σ_{k≤m<i}R_{k,m}` and `b_k = g_k + Σ_{m≥i}R_{k,m}`.
  - `z_kR_{k,m} = c_k^{(m)}`, so `f_k ∈ M_{D_i}` and `v_k^*v_k = v_kv_k^* = b_k`.
- **Lemma 5 (RFD).**
  - **Amalgam.** A representation of `W^{(k−1)} *_{ℂ²} (C(𝕋)⊕ℂ)` is a pair `(σ, V)` with `V` a unitary on the range of `σ(b_k)`. So the iterated amalgam is the universal `W_i`.
  - **Embeddings.** For `k < i`, `0 < τ(b_k) < 1`, so `ℂ² ↪ M_{D_i} ↪ W^{(k−1)}` is a unital embedding.
    - Every unital `σ_n` is faithful on the simple `M_{D_i}`, so `P_n ≠ 0` and `1−P_n ≠ 0`.
    - `q_2` is injective: spectra are dense and `1−P_n ≠ 0`. It is unital, and `q_1(b_k) = (P_n)_n = q_2(1,0)`.
    - Li–Shen Theorem 2 applies: separable unital factors, finite-dimensional amalgam, compatible unital embeddings into one `∏M_{d_n}`. Its hypotheses were checked against the reviewed node.
    - For `k = i`, `b_i = 1` and Exel–Loring applies.
  - **Separating sequence.** A separable RFD algebra has an isometric separating sequence: norm a dense sequence to within `1/n`.
- **Lemma 6 (C2).**
  - `Q = ∏_{i≤i'<m}(1−p_{i'})p_m` commutes with `A_i` by Lemma 1, since `k ≤ i ≤ i'`.
  - `b_kQ = R_{k,m}`, so `v_kQ = z_kR_{k,m} = c_k^{(m)} = c_k^{(m)}Q`.
  - `A_iQ ⊆ QM_{D_{m+1}}Q` acts on `ran Q ≅ ℂ^{D_i}⊗E_m`.
  - `ℂ^{D_i}⊗ℂ^t` is reducing, because one isometry `ℂ^t ↪ E_m` serves all `k` at step `m`. The representation there agrees with `ρ^{(i)}_n` on the generators, hence everywhere.
  - Since `Q ≤ e_m` and `e_m` commutes with `A_i`: `‖ρ(w)‖ ≤ ‖q(w)Q‖ ≤ ‖q(w)e_m‖`.
  - The chain `‖w‖ ≤ sup_{m≥i}‖q(w)e_m‖ ≤ ‖q(w)‖ ≤ ‖w‖` makes `q` isometric. For `x ≠ 0` some `e_mxe_m = xe_m ≠ 0`.

## 2. The comb criterion and its hypotheses
- **Hypotheses.**
  - `e_i = p_i ∈ N_i ⊆ A_{i+1}`.
  - `e_i` commutes with `A_i`, and `e_iA_ie_i ≅ M_{D_i}` is simple with unit `e_i` (Lemma 2).
  - Separation holds by Lemma 6, and fullness in `A` by Lemma 3.
- **Criterion re-derived** (sk-verify-16 PASS).
  - **Simplicity.** If `J ∩ A_i = 0` for all `i`, the quotient map is isometric on `⋃A_i`, so `J = 0`. Otherwise take `0 ≠ x ∈ J∩A_i`. Then `0 ≠ xe_j ∈ J ∩ e_jA_je_j`, so `e_j ∈ J`, and fullness gives `1 ∈ J`.
  - **Local quantization.** `B = e_iA_ie_i` with the `η/3` approximation.
- **Definition.** It matches the one read at source: Brown–Dykema math/0207005 l.219–224 (nonzero finite-dimensional `B`, inclusion not necessarily unital, `‖[x,e]‖ < ε`, `dist(exe,B) < ε`).

## 3. Fixes
- **F1, schedule (§4).**
  - π cannot be total. At `m = 1`, `i = 1` and the bound is the empty product 1, so `π(1)` exists only if some `t^{(1)}_n = 1`.
  - Fix: make π a partial map onto `{(i,n)}` and put `c_k^{(m)} := R_{k,m}` at idle steps.
  - Surjectivity still holds, since each pair is admissible for all large `m`. Lemmas 1, 2, 4 and 6 are unchanged.
- **F2, scope (add to §6).** The answer is to the question as printed. Brown–Dykema's extra property (II), WEP of `M` relative to `A`, is not claimed and cannot hold in general:
  - For weakly dense `A`, (II) is equivalent to amenability of `τ|_A` (math/0207005 Theorem `mainthm` (3)–(4), l.1467–1515, via Kirchberg).
  - Amenability of `τ|_A` embeds `M` in `R^ω`.
  - So in a separable II_1 factor not embeddable in `R^ω` (these exist by MIP* = RE; recalled, not source-checked), no weakly dense subalgebra has (II).
  - Also, for `M ≇ R`, `A` cannot be locally reflexive with `τ|_A` amenable (memoir math/0304009 l.4630–4642, Corollary `locallyreflexive`).
  - Theorem P claims neither, so there is no conflict.
- **F3, locator.**
  - Cite the question as arXiv:math/0111286v3, §Questions, item 3 (l.3134, re-read here verbatim: "Can a free group factor or a II$_1$ factor with property T contain a weakly dense, QD C$^*$-subalgebra? How about a Popa algebra?").
  - The memoir e-print has no string `weakly dense, QD` (grep).
  - Brown–Dykema cite the non-McDuff clause as "Question 11.1 in [brown:AFDtraces]" (l.228–230).
- **F4, novelty.** Keep "not found in a bounded search" (§5). No priority claim without MathSciNet citation lists of Popa 1997 and Brown–Dykema.

## 4. Consistency with the firewalls
- **Gamma firewall G** (sk-popa-lgx §2): not triggered. G needs matrix units on `q_i` commuting with `q_iA_iq_i`, with `τ(1−q_i) → 0`. The natural candidate is `q_i = 1−p_i` with the matrix units of `(1−p_i)N_i(1−p_i)`, and it fails:
  - the tail blocks `c_k^{(m)}`, `m > i`, mix the `i`-th tensor factor through `ℂ^t ↪ E_m`;
  - `u_k` is arbitrary on `g_k`.
- **O** (`kazhdan-generators-admit-no-norm-popa-corners`): no norm approximation is claimed. `z_k` differs from `y'_k` by blocks on `1−g_k`.
- **S′** (`orthogonal-popa-corners-for-kazhdan-approximants-small-trace`):
  - `(R_{K,m}, R_{K,m}M_{D_{m+1}}R_{K,m})_m` is an orthogonal family of exact (`η = 0`) Popa corners for `z_1..z_K`, with total trace `τ(1−g_K)`.
  - S′ forces `Σ_s(‖a_sP‖_2²+‖Pa_s‖_2²) ≥ ε²τ(1−g_K)/2` on `P = 1−g_K`: the blocks must be relatively bad approximants.
  - Theorem P claims nothing about the blocks, and its bound `‖z_k−y'_k‖_2² ≤ 16τ(1−g_k)` has the same order. S′ explains why weak density cannot beat `O(τ(1−g_k)^{1/2})`.
- **Corner traces:** `τ(e_j) = 1/r_j ≤ Σ_{i'≥k}1/r_{i'}` for `k ≤ j`.
- **Ozawa, arXiv:2609.08892 (2026), "R is not quasidiagonal":** no conflict, since `A` is separable.

## 5. Bounded novelty check
- **Citing papers (Semantic Scholar).**
  - Brown–Dykema math/0207005: 56 listed.
  - Brown memoir math/0304009: filtered titles, namely Ozawa 2026, Farah–Hirshberg 2019, Chen–Ng 2020.
  - Brown math/0111286: 3 indexed.
  - None states weakly dense Popa algebras in all separable II_1 factors or in any property (T) factor.
- **Web searches.**
  - "weakly dense Popa algebra";
  - "quasidiagonal weakly dense C*-subalgebra property (T) II_1 factor Brown question";
  - "Popa algebra property (T) factor weakly dense simple quasidiagonal subalgebra";
  - "every separable II_1 factor contains a weakly dense simple quasidiagonal C*-subalgebra local quantization";
  - "Popa algebras II_1 factor property T weakly dense answer Brown question 2020–2025".
  - Only Brown (McDuff) and Brown–Dykema (`L(F_s)`) turned up.
- **Popa 1997.** Located, Pacific J. Math. 181 (1997) 141–158; the text was not re-read.
- **Memoir e-print.**
  - l.392–432: the expectation `M ≅ R` fails.
  - l.562–596: relative WEP, McDuff and Brown–Dykema.
  - No general existence statement.

## 6. Outside the queue: a false reason in `separable-ii1-factors-have-weakly-dense-full-free-group-cstar`
- **The bullet.** The node's "Statement fidelity" bullet says that an amenable trace on a weakly dense subalgebra forces `M ≅ R`, citing memoir l.4636.
- **Why it is false as stated.**
  - `τ|_{A_s}` is amenable for Brown–Dykema's `A_s ⊆ L(F_s)` (Theorem `mainthm` (3)), yet `L(F_s) ≇ R`.
  - The memoir result at l.4630–4642 needs local reflexivity.
- **What stands.** The bullet's conclusion, that no trace condition is meant, is right. Replace the reason by "Brown–Dykema's examples live in non-injective factors".
- Not merged; main decides.
