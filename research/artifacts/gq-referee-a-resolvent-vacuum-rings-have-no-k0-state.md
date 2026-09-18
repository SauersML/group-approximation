# Referee report (gq-referee-a, proof-gap lens): resolvent-vacuum rings have no K_0 state

**Reviewed:** `resolvent-vacuum-rings-have-no-k0-state` and its route `-proof` (lane gq-ring-fp-simple, b936655b4),
read on origin/main.

**Verdict: PASS.** No gaps found. There is one naming note (§4).

## 1. Orthogonal copies
- **Idempotents.** Since `x_m E = x_m`, `P_m^2 = x_m E y_m = P_m`.
- **Orthogonality.** Evaluate `y_m N x_{m'}` in two ways: it equals `λ_{m'} y_m x_{m'}` and `λ_m y_m x_{m'}`.
  - The `λ` are central integers and their differences are non-zero-divisors, so `y_m x_{m'} = 0`.
  - Hence `P_m P_{m'} = 0`.
- **Equivalence.** Left multiplication by `x_m` maps `ER → P_m R`, because `x_m r = P_m x_m r`. Left multiplication
  by `y_m` maps `P_m R → ER`. Both composites are the identity. So `P_m ~ E`.
- **Counting.** Orthogonal idempotents give the decomposition `R = ⊕_{i ≤ M} P_i R ⊕ (1 − ΣP_i)R`. So `M[E] ≤ [1]`.

## 2. A full vacuum
- **Fullness.** `1 = Σ a_i E b_i` makes `(ER)^k → R` surjective, and it splits because `R` is free. So `[1] ≤ k[E]`.
- **(b) No state.** Evaluate a state on the two inequalities: `2k f(E) ≤ 1 ≤ k f(E)`. So `f(E) ≤ 0`, which
  contradicts `k f(E) ≥ 1`.
- **(a) Direct-summand bookkeeping (author's point (a)).** Correct. We have `P = (ER)^k ≅ R ⊕ Z` and
  `R ≅ (ER)^{2k} ⊕ Y = P ⊕ P ⊕ Y`. So `P ≅ P ⊕ (P ⊕ Y ⊕ Z)`.
  - This gives a split injection `P → P` whose cokernel is nonzero, because `P ≠ 0`.
  - Hence `End(P) ≅ e M_k(R) e`, with `e = diag(E, …, E)`, is not directly finite.
- **Corners (author's point (b)).** The direction is correct.
  - If `ba = e` in `eSe`, put `a' = a + (1−e)` and `b' = b + (1−e)`. Then `b'a' = 1`.
  - So direct finiteness of `S` gives `a'b' = 1`, hence `ab = e`.
  - By the contrapositive, `M_k(R)` is not directly finite.

## 3. The instances (author's point (c))
- **`R_L`.**
  - `N s_1^{m−1} = s_1^{m−1}(N + m − 1)` and `N s_2 = 0`, so `N x_m = (m−1) x_m`.
  - `N = s_1(N+1)t_1` gives `t_1 N = (N+1) t_1` and `t_2 N = 0`, so `y_m N = (m−1) y_m`.
  - `y_m x_m = 1`.
- **The Toeplitz ring.**
  - From `N = N(ST + E)` and `NE = 0` we get `N = S(N+1)T`. So `TN = (N+1)T`, and `EN = N − S(N+1)T = 0`.
  - Both identities then hold with `λ_m = m − 1`.
  - Differences of integers are units in the concrete model, which is a `Q`-algebra.
  - `E` is not full, and the node says so.
- **`R_k`.**
  - (Cov) gives `N s_n = s_n(N+1)`, `N s_v = 0`, `t_n N = (N+1)t_n` and `t_v(N + c) = c·t_v`.
  - So `x_m = s_n^{m−1} s_v` and `y_m = t_v t_n^{m−1}` work with `λ_m = m − 1`.
  - `E = 1` is full.

## 4. Scope and a naming note
- **Scope.** The consequences are correctly limited. A ring that gets `Q` from a full resolvent vacuum has no state
  on `K_0`, so no normalized trace or dimension function, and it is not stably finite.
- **Consistency.** The SL_3 Toeplitz harmonic ring of `sl3-toeplitz-harmonic-ring-is-simple-and-k1-rational` is
  tracial, so it carries no full resolvent vacuum. It gets `Q` by harmonic elimination instead.
- **Naming.** That ring is also called `R_T` on main. The same name for the Toeplitz ring
  `q-embeds-in-a-corner-of-a-fp-toeplitz-ring` invites confusion. Consider renaming one of them in the instances list.
