---
rg: 2
id: mersenne-stretch-forces-periodic-point-in-linear-spacetimes
kind: claim
title: In a linear quasigroup spacetime over F_q, one row with a long (q^k - 1)-periodic stretch forces a periodic point, so aperiodic Ledrappier sub-SFTs have no 2-uniform-substitutive rows
distinct_from:
  permutive-triangle-sfts-are-quantum-rigid: that needs a whole periodic row or column; this needs only a finite periodic stretch of length 2m+L-1 with m = q^k - 1 in one row, for linear rules.
  small-window-quasigroup-sub-sfts-have-periodic-points: that is an exhaustive search over small windows; this is a proof for every window L, restricted to the linear class, and it kills every 2-uniform-substitutive row seed.
  triangle-permutive-sfts-have-one-sided-total-faults: that gives general structure (RPCA form, faults, complexity); this is a Frobenius-specific periodicity obstruction.
artifacts:
  - experiments/quasigroup-window-extension-2026-09-17/tm_ledrappier.py
  - experiments/quasigroup-window-extension-2026-09-17/seeded_rows.py
---

**ESTABLISHED (lane proof, swarm-0917-w12-w12-bh-follow, unreviewed, no priority claimed).**

**Setting.**

- Let `q` be a prime power and `α, β ∈ F_q^×`, and set `x ⋆ y = αx + βy`. This is a Latin square on `F_q`. For
  `q = 2` it is Ledrappier's rule.
- Let `X_⋆ = {x : x(z+e_2) = x(z) ⋆ x(z+e_1)}`. Row `t+1` of a point is `F(row_t)`, where `F = α + βσ` and
  `(σr)_i = r_(i+1)`.
- For `A ⊆ F_q^L`, let `Ω(A)` be the set of points of `X_⋆` whose rows have all their length-`L` words in `A`. By
  the normal form in `small-window-quasigroup-sub-sfts-have-periodic-points`, every sub-SFT of `X_⋆` with
  forbidden patterns supported in translates of `Δ_L` has this form.

**Theorem.** Let `m = q^k - 1` with `k >= 1`. Suppose some row `x` of a point of `Ω(A)` agrees with an
`m`-periodic sequence `p` on an interval of length `2m + L - 1`. Then `Ω(A)` has a doubly periodic point, with
spatial period dividing `m` and temporal period dividing `m`.

**Corollaries.**

1. **Zero word.** Suppose `q = 2`, and some row `x` of a point of `Ω(A)` has `x[i, i+L) = x[i+2^k, i+2^k+L)` for
   some `i` and some `k >= 0`. Then `0^L ∈ A`, so the zero point lies in `Ω(A)`.
2. **Substitutive rows are killed.** Let `θ` be a primitive, aperiodic, 2-uniform substitution on `{0,1}`, such as
   Thue–Morse or period doubling. If some row of an aperiodic `Ω(A) ⊆` Ledrappier lay in the subshift `X_θ`, then
   `Ω(A)` would contain the zero point, a contradiction. So no aperiodic Ledrappier sub-SFT has a row in `X_θ`.
3. **Periodic stretches are banned.** For `q = 2`, the rows of an aperiodic `Ω(A)` contain no `m`-periodic stretch
   of length `2m + L - 1` for any `m ∈ {1, 3, 7, 15, …}`. For `m = 1` this means every run of one letter has
   length at most `L`.

## Proof

**Step 1 (Frobenius).** The maps `α·id` and `βσ` are commuting `F_q`-linear operators on `F_q^Z`. Since `q^k` is a
power of the characteristic `p`, every binomial coefficient `C(q^k, j)` with `0 < j < q^k` vanishes mod `p`. Hence
`F^(q^k) = α^(q^k) + β^(q^k) σ^(q^k) = α + βσ^(q^k)`, because `c^(q^k) = c` for `c ∈ F_q`. On `m`-periodic
sequences `σ^(q^k) = σ^(m+1) = σ`, so there `F^(q^k) = F`, that is `F^(m+1) p = F p`.

**Step 2 (locality).** `(F^j r)_i` depends only on `r[i, i+j]`. So the word `(F^j r)[i, i+L)` depends only on
`r[i, i+j+L-1]`.

**Step 3.** Let `x` agree with `p` on `[a, a + 2m + L - 1)`. Fix `j` with `1 <= j <= m`, and fix `i` with
`a <= i < a + m`. Then `[i, i+j+L-1] ⊆ [a, a+2m+L-1)`. Row `j` above `x` in the same point is `F^j x`, so
`(F^j p)[i, i+L) = (F^j x)[i, i+L) ∈ A`. The sequence `F^j p` is `m`-periodic, and `i` runs over all residues
mod `m`. So every length-`L` word of `F^j p` lies in `A`, for `1 <= j <= m`.

**Step 4 (the point).** Define `z(·, t) = F^(1 + (t mod m)) p`. Then `z(·, t+1) = F z(·, t)` for all `t`:

- for `t mod m < m - 1` this is immediate;
- for `t mod m = m - 1` it reads `F^1 p = F^(m+1) p`, which is Step 1.

So `z ∈ X_⋆`. By Step 3 all its row words lie in `A`, so `z ∈ Ω(A)`. It is doubly periodic, with spatial period
dividing `m` and temporal period dividing `m`. ∎

**Corollary 1.** For `q = 2`, `F^(2^k) = 1 + σ^(2^k)`. The row `F^(2^k) x` lies in the same point, and
`(F^(2^k) x)[i, i+L) = x[i, i+L) + x[i+2^k, i+2^k+L) = 0^L`. So `0^L ∈ A`. The zero point has only the row words
`0^L`, and `F(0) = 0`, so it lies in `Ω(A)`. ∎

**Corollary 2.** The language of `X_θ` contains `aa` for some letter `a`. Otherwise every word alternates, and
`X_θ` is periodic. The language is closed under `θ`, so it contains `θ^k(a) θ^k(a)`, whose two halves are equal
words of length `2^k`. By primitivity, `X_θ` is minimal, so every `x ∈ X_θ` contains this word, say at position
`s`. Choose `2^k >= L`. Then `x[s, s+L) = x[s+2^k, s+2^k+L)`, and Corollary 1 applies. ∎

**Corollary 3** is the Theorem with `q = 2`. ∎

## Computation

- **Run.** `experiments/quasigroup-window-extension-2026-09-17/tm_ledrappier.py 6 30 16384 2048` builds the
  Thue–Morse Ledrappier point `y(·, n) = F^n TM`, which is fixed by the dilation `x ↦ x(2·)` because
  `TM(2i) = TM(i)`. It takes `A_6` to be the words of `y`: 54 of 64. The run finds the fixed point `0` at `m = 1`,
  as Corollary 2 predicts.
- **Word counts.** `seeded_rows.py` records the missing-word counts of `∪_n F^n(seed)`:
  - Thue–Morse misses a word from `L = 6`;
  - period doubling misses a word from `L = 4`;
  - Fibonacci misses nothing up to `L = 12`.
  Every such window set for the 2-uniform seeds contains `0^L`, by Corollary 2.

## What this changes

- **Self-similar seeds are dead.** The natural self-similar seeds for an aperiodic Ledrappier sub-SFT are dead for
  every window `L`. These are rows from primitive 2-uniform substitutions, including the Thue–Morse `D_2`-fixed
  point.
- **A necessary condition.** In an aperiodic Ledrappier `Ω(A)`, every row avoids two things:
  - an `L`-word repeat at any distance `2^k`;
  - a `(2^k - 1)`-periodic stretch of length `2^(k+1) + L - 3`.

  So row structure must be "dyadically non-recurrent".
- **Heuristic only.** Hierarchical constructions whose zoom factors are powers of 2 look incompatible with
  Ledrappier's shift. I have proved this only for substitutive rows, not for general self-simulating hierarchies.
- **Scope.** This constrains the linear class only. General Latin squares have no Frobenius identity.
