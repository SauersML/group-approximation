---
rg: 2
id: burau-power-projective-ping-pong-needs-cubes-proof
kind: route
title: "Eigenflag incidence obstruction for squares, plus the Beridze–Bigelow–Traczyk valuation sets for cubes"
target: burau-power-projective-ping-pong-needs-cubes
requires: []
artifacts:
  - research/artifacts/burau-power-projective-ping-pong-2026-09-16.md
  - experiments/zaremsky-3-05-burau-squares-2026-09-16/threshold_verify.py
  - experiments/zaremsky-3-05-burau-squares-2026-09-16/bbt_sets_test.py
---

Direct proof. Full details and explicit matrices are in the artifact.

## Obstruction lemma

**Setup.** `a` is diagonal with eigenpoints `p_+, p_0, p_-`, whose
eigenvalues have strictly decreasing absolute values. Put
`ℓ_+ = p_+ p_0` and `ℓ_- = p_0 p_-`.

**Hypotheses.**

- (i) `b ℓ_± != ℓ_±`.
- (ii) Either:
  - (ii-a) for some `ε`, `b^ε p_+ ∈ ℓ_+ \ {p_+}` and
    `b^{-ε} p_- ∈ ℓ_- \ {p_-}`; or
  - (ii-b) some `b^{±1}` maps `p_+` or `p_-` onto `p_+` or `p_-`.

**Conclusion.** No 4-set ping-pong for `(a, b)` has `X_{a±}` closed.

**Proof.**

1. **Where `p_±` lie.** Iterate `a` on `X_{a+} ∪ X_{b±}`.
   - If some point lies off `ℓ_-`, its iterates converge to `p_+`, so
     `p_+ ∈ X_{a+}`.
   - Otherwise `X_{a+}` and `X_{b+}` both lie in the single point
     `ℓ_- ∩ b^{-1} ℓ_-`, which contradicts disjointness.
   - Symmetrically, `p_- ∈ X_{a-}`.
2. **Case (ii-b).** Some `p_±` lies in `X_{a±} ∩ X_{b±}`, a contradiction.
3. **Case (ii-a).**
   - `a^{-j} b^ε p_+ ∈ X_{a-}` converges to `p_0`.
   - `a^j b^{-ε} p_- ∈ X_{a+}` converges to `p_0`.
   - Closedness puts `p_0` in both sets, a contradiction.

## Application

Specialize at `t_0` with `|t_0| != 1`. Every entry claimed nonzero is
`± t^c` times a product of cyclotomic polynomials, so it cannot vanish.

- **`n = 1`.** `k e_1 = e_3`, so (ii-b) holds.
- **`n = 2`.** (ii-a) holds with `ε = +1`:
  - `k^2 e_1 = (-(t^2+t+1)/t, (t+1)(t^2+1)/t^2, 0)`;
  - `k^{-2} e_3 = (0, (t+1)(t^2+1)/t^2, -(t^2+t+1)/t)`.
- **(i).** It holds via the entries of `k^n e_2`.
- **Dual plane.** Use the rows of `k^{±n}` in the same way.
- **Consequence.** If `n <= 2`, the sets `X_{f±}` cannot both be closed.
- **The case `m <= 2`.** Conjugation by `s`, using `s^{-1} f s = k^{-1}` and
  `s^{-1} k s = f`, turns a configuration for `(f^m, k^n)` into one for
  `(f^n, k^m)` and swaps the roles of the `f`-sets and `k`-sets.
- **The pair `(A, B)`.** `P(-t_0)` conjugates `(A, B)` at `t_0` to `(f, k)` at
  `-t_0`. It is invertible because `det P = -t^2(t-1)^2(t^2+1)`.

## Existence for `m, n >= 3`

Work over `F((t))` with `v` the lowest degree. Set
`X_1 = {v_1 <= v_2 - 2, v_1 <= v_3 - 2}` and let `X_2`, `X_3` be BBT's other
sets.

- **Inclusions.**
  - `T X_1 ⊆ X_2` and `T^{-1} X_1 ⊆ X_3`.
  - `B` maps `Y_d` into `Y_{d+1}`.
  - `B X_2 ⊆ Y_1` and `B X_3 ⊆ X_2`.
  - So `B^n (X_1 ∪ X_2 ∪ X_3) ⊆ X_1` for `n >= 3`.
- **The configuration.** Take `S_{B+} = X_1`, `S_{A+} = T X_1`,
  `S_{A-} = T^{-1} X_1` and `S_{B-} = T^2 X_1`. With `T^4 = 1`,
  `A = T B T^{-1}` and `B^{-1} = T^2 B T^2`, these give a clopen 4-set
  ping-pong for `(A^m, B^n)`.
- **Transfer.** Apply `t -> -t`, which preserves `v`, and then `P`.

## Checks

Exact sympy verification of all matrices and vectors: `threshold_verify.py`.
Randomized exact test of the set inclusions over `Z` and `F_2, F_3, F_5`:
`bbt_sets_test.py`. Both exit 0.
