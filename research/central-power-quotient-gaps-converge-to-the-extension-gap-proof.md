---
rg: 2
id: central-power-quotient-gaps-converge-to-the-extension-gap-proof
kind: route
title: Lift corona unitaries by polar parts for compactness, and round the z-letter by Borel functional calculus to an exact m-th root of unity for the gap inequality
target: central-power-quotient-gaps-converge-to-the-extension-gap
requires: []
artifacts:
  - experiments/central-rounding-2026-09-17/check_rounding.py
---

Notation is as in the target. `Q = ∏_n M_{k_n} / ⊕_n M_{k_n}` is a norm matrix corona. Its norm
is `||[x_n]|| = limsup_n ||x_n||`.

**Step 0 (two standard facts).**
- (F1) Every unitary `u ∈ Q` lifts to a sequence of unitaries. Take any bounded lift `(x_n)`.
  Then `||x_n^* x_n − 1|| → 0` and `||x_n x_n^* − 1|| → 0`, so `x_n` is invertible for large `n`.
  Its polar part `v_n = x_n |x_n|^{-1}` is unitary with `||v_n − x_n|| ≤ ||x_n|| · || |x_n|^{-1} − 1 || → 0`.
  Put `v_n = 1` for the finitely many other `n`.
- (F2) For a finite matrix `A` and words `w` in unitaries, replacing one letter `A` by `A'` (or
  `A^{-1}` by `A'^{-1}`) changes the value of `w` in norm by at most `||A − A'||`. This holds
  because the other letters are unitary, and `||A'^{-1} − A^{-1}|| = ||(A' − A)^*|| = ||A' − A||`
  when `A, A'` are unitary. Telescoping gives: if `A` occurs `ℓ` times with sign `±1`, the change
  is at most `ℓ ||A − A'||`.

**Step 1 (item 1, compactness).**
- *If some `δ_∞(c) = 0`, then `z ∉ Rad(G)`.* Choose `U^{(n)} ∈ U(k_n)^S` with
  `||U^{(n)}_z − 1|| ≥ c` and `def_R(U^{(n)}) ≤ 1/n`. Put `ρ(s) = [U^{(n)}_s]_n ∈ U(Q)`. For
  `r ∈ R`, `||r(ρ) − 1|| = limsup_n ||r(U^{(n)}) − 1|| = 0`. So `ρ` factors through `G`, and
  `||ρ(z) − 1|| = limsup_n ||U^{(n)}_z − 1|| ≥ c > 0`.
- *If `z ∉ Rad(G)`, then some `δ_∞(c) = 0`.* Let `ρ : G → U(Q)` with `c_1 = ||ρ(z) − 1|| > 0`.
  By (F1), lift each `ρ(s)` to unitaries `(V^{(n)}_s)_n`. For each `r ∈ R`,
  `limsup_n ||r(V^{(n)}) − 1|| = ||r(ρ) − 1|| = 0`, so `def_R(V^{(n)}) → 0` (`R` is finite). And
  `limsup_n ||V^{(n)}_z − 1|| = c_1`, so infinitely many `n` have `||V^{(n)}_z − 1|| ≥ c_1/2`.
  Along those `n`, `def_R → 0`, so `δ_∞(c_1/2) = 0`.
- The same argument, with relator set `R ∪ {z^m}`, gives the statement for `G_m`.

**Step 2 (item 2, the rounding inequality).**
- *Lower bound.* `def_m ≥ def_R` pointwise, so `δ_m(c) ≥ δ_∞(c)`.
- *Upper bound.* Let `f_m : S^1 → S^1` send `e^{iθ}`, with `θ ∈ [−π/m + 2πj/m, π/m + 2πj/m)`, to
  `e^{2πij/m}`. It is Borel, and `|f_m(λ) − λ| ≤ |e^{iπ/m} − 1| ≤ π/m`. Let `U ∈ U(k)^S` with
  `||U_z − 1|| ≥ c + π/m`. Define `U'` by `U'_s = U_s` for `s ≠ z` and `U'_z = f_m(U_z)`, using
  the spectral decomposition of the unitary matrix `U_z`. Then:
  - `U'_z` is unitary, `(U'_z)^m = 1` exactly, and `||U'_z − U_z|| ≤ π/m`;
  - `||U'_z − 1|| ≥ ||U_z − 1|| − π/m ≥ c`;
  - by (F2), `||r(U') − 1|| ≤ ||r(U) − 1|| + Lπ/m` for each `r ∈ R`.

  So `def_m(U') = def_R(U') ≤ def_R(U) + Lπ/m`. Taking the infimum over `U` gives
  `δ_m(c) ≤ δ_∞(c + π/m) + Lπ/m`.
- *Convergence.* As `m → ∞`, `δ_∞(c + π/m) → δ_∞(c+)`, the right limit, which exists by
  monotonicity. So `δ_∞(c) ≤ liminf δ_m(c) ≤ limsup δ_m(c) ≤ δ_∞(c+)`. A monotone function has
  at most countably many discontinuities.

**Step 3 (item 3).**
- (a) ⇒ (b): `δ_m(c) ≥ δ_∞(c) > 0` by Step 2 and Step 1.
- (b) ⇒ (c): `m δ_m(c) ≥ m · inf_{m'∈M} δ_{m'}(c) → ∞`.
- (c) ⇒ (d): for large `m ∈ M`, `m ≥ π/c` and `m δ_m(c) > Lπ`.
- (d) ⇒ (a): suppose (a) fails. By Step 1, `δ_∞(c_0) = 0` for some `c_0 ∈ (0,2)`, hence for all
  `c ≤ c_0` by monotonicity. Let `c = c_0/2` and `m ≥ π/c`. Then `π/m ≤ c`, so
  `c + π/m ≤ c_0 < 2`, and Step 2 gives `δ_m(c) ≤ δ_∞(c_0) + Lπ/m = Lπ/m`. So (d) fails at
  `c = c_0/2`.

**Step 4 (item 4).** If (a) holds, the first alternative holds by Steps 1 and 2. If (a) fails,
the computation in (d) ⇒ (a) gives the second alternative for every `c ≤ c_0/2`. They cannot
both hold: the second gives `δ_∞(c) ≤ δ_m(c) ≤ Lπ/m → 0` for small `c`. ∎

**Remark (nothing about `z` beyond the presentation is used).** Centrality, perfectness and
Property `(T)` play no role. Centrality only matters for identifying `⟨⟨z^m⟩⟩ = ⟨z^m⟩` in
applications.
