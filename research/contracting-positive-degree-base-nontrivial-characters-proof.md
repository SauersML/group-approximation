---
rg: 2
id: contracting-positive-degree-base-nontrivial-characters-proof
kind: route
title: Certify the nuclei, solve the nucleus system for the sum-invariant characters, and push the t-exponent sum to V_{3,r}G by cone tables
target: contracting-positive-degree-base-nontrivial-characters
requires:
  - sum-invariant-characters-of-contracting-groups-via-nucleus
  - rover-nekrashevych-characters-are-sum-invariant
artifacts:
  - experiments/contracting-polynomial-activity-2026-09-17/autgrp.py
  - experiments/contracting-polynomial-activity-2026-09-17/sumchar.py
  - experiments/contracting-polynomial-activity-2026-09-17/relsearch.py
  - experiments/contracting-polynomial-activity-2026-09-17/verify_example.py
  - experiments/contracting-polynomial-activity-2026-09-17/verify_example.out
  - experiments/contracting-polynomial-activity-2026-09-17/tower2.py
---

Notation is that of the claim. `(gh)|_x = g|_{h(x)} h|_x`, and `T = t^{-1} = (T, 1, 1)(0 2 1)`.

## 1. Activity (by hand)

- `t` has exactly one nontrivial section at each level, at `2^k`. So `θ_k(t) = 1`, and the same holds for `T`.
- `a|_{0^k} = a`. At `0^j 1` and `0^j 2` the sections are `t` and `T`, each with one nontrivial section per further
  level. So `θ_k(a) = 1 + 2k`.
- `b|_{1^k} = b`. At `1^j 0` and `1^j 2` the section is `a`, which contributes `θ_{k−j−1}(a)` at level `k`. So

      θ_k(b) = 1 + 2 Σ_{m=0}^{k−1} (2m + 1) = 1 + 2k^2.

- Elements of degree `<= n` form a subgroup, since `θ_k(gh) <= θ_k(g) + θ_k(h)`. So every element of `G_1` has
  degree `<= 1`, and every element of `G_2` has degree `<= 2`. The generators `a` and `b` attain these degrees.
- `t` has degree 0, so `t in (G_i)_0`.
- The script recomputes this from the minimized automaton: its states have degrees `0, 0, 1` and `0, 0, 1, 2`.
- `a` and `b` are involutions:
  - `a^2 = (a^2, T t, t T)`, the identity by induction;
  - `b^2 = (a a, b^2, a a)`, also the identity.

## 2. Contraction (exact certificate)

Let `N_1 = {1, t, T, a, at, Ta, Tat}` and `N_2 = N_1 ∪ {b}`. The recursions in the claim's table are checked by hand
from `(gh)|_x = g|_{h(x)} h|_x`. For example, `at`:

- `t(0) = 1`, so the section at 0 is `a|_1 t|_0 = t`;
- `t(1) = 2`, so the section at 1 is `a|_2 t|_1 = T`;
- `t(2) = 0`, so the section at 2 is `a|_0 t|_2 = at`;
- the root permutation is `x ↦ a(t(x))`, which is `(0 2)`.

So each `N_i` is closed under sections and contains the cycle states of the generating automaton.

`verify_example.py` finds each `N_i` as the least fixed point of `N ← N ∪ (cycle states of N·N, closed under
sections)`, starting from the generators' cycle states. In particular, for all `n_1, n_2 in N_i` every cycle state of
`n_1 n_2` lies in `N_i`. By the contraction certificate of `sum-invariant-characters-of-contracting-groups-via-nucleus`,
`G_i` is contracting, and `N_i` contains all eventual sections.

Equality of elements is decided exactly by Moore minimization (see that route), so the certificate is exact.

## 3. Sum-invariant characters

Apply the theorem of `sum-invariant-characters-of-contracting-groups-via-nucleus` to `N_i`.

**(i) by hand.** Put `I(t) = 1`, `I(T) = −1`, `I(a) = 0`, `I(at) = 1`, `I(Ta) = −1`, `I(Tat) = 0` and `I(b) = 0`.
Then `I(n) = Σ_x I(n|_x)` for each of these:

| `n` | Sum over sections | Value |
|---|---|---|
| `t` | `0 + 0 + 1` | 1 |
| `T` | `−1 + 0 + 0` | −1 |
| `a` | `0 + 1 − 1` | 0 |
| `at` | `1 − 1 + 1` | 1 |
| `Ta` | `−1 + 1 − 1` | −1 |
| `Tat` | `1 − 1 + 0` | 0 |
| `b` | `0 + 0 + 0` | 0 |

**(ii) by computer.** The system (i)+(ii) is solved over `Fraction` for all ordered pairs in `N_i`. The solution space
is one-dimensional in both cases, spanned by the `I` above (`verify_example.out`).

So the sum-invariant characters of `G_i` are `Q χ`, where `χ = χ_I`. On generators, `χ(t) = 1` and
`χ(a) = χ(b) = 0`. So `χ` is the `t`-exponent sum, and every relation of `G_i` has `t`-exponent sum 0.

**Sanity check, independent of the theorem.** `relsearch.py` groups all reduced words of length `<= 16` (for `G_1`)
and `<= 10` (for `G_2`) by the element they define. No two words defining the same element have different
`t`-exponent sums.

## 4. From `χ` to `V_{3,r}G_i`, for every `r`

**Setup.** Let `G` be self-similar and faithful on `X_d^*`, and `C = X_r × X_d^ω`.

- An element `h` of `V_{d,r}G` has a *table*: cone partitions `C = ⊔_i C_{α_i} = ⊔_i C_{β_i}` and `g_i in G` with
  `h(α_i w) = β_i g_i(w)`.
- For a sum-invariant `χ`, put `Φ_χ(h) = Σ_i χ(g_i)`.

**Lemma.** `Φ_χ` is a well-defined homomorphism `V_{d,r}G -> Q`. It satisfies `Φ_χ(g_(α)) = χ(g)`, where `g_(α)` acts
as `αw ↦ α g(w)` on `C_α` and as the identity elsewhere.

*Proof.*

- **Refinement.** Replacing row `i` by its `d` children `α_i x ↦ β_i π_{g_i}(x)`, with elements `g_i|_x`, changes the
  sum by `Σ_x χ(g_i|_x) − χ(g_i) = 0`.
- **Well-defined.** Two tables of `h` have domain partitions with a common refinement by splitting. On a fixed domain
  partition the table is unique:
  - `C_{β_i} = h(C_{α_i})` determines `β_i`;
  - faithfulness then determines `g_i`.
- **Additivity.** Let `h` have table `(γ_j, δ_j, g'_j)` and `h'` have table `(α_i, β_i, g_i)`. Refine the table of
  `h'` until every `|β_i| >= max_j |γ_j|`. Then `β_i = γ_j u` for a unique `j`, and

      h h'(α_i w) = δ_j g'_j(u) · g'_j|_u g_i(w).

  - So `Φ_χ(hh') = Σ_i χ(g_i) + Σ_i χ(g'_j|_u)`.
  - The rows `γ_j u ↦ δ_j g'_j(u)` with elements `g'_j|_u`, one for each `i`, form a table of `h`, because the
    `C_{β_i}` partition `C`.
  - So the last sum is `Φ_χ(h)`, and `Φ_χ(hh') = Φ_χ(h) + Φ_χ(h')`.
- **The value on `g_(α)`.** `g_(α)` has the table consisting of the row `α ↦ α` with element `g`, and identity rows on
  a cone partition of `C \ C_α`.

∎

## 5. Conclusion

- Apply the Lemma to `χ` on `G_i`, with `d = 3`. Then `Φ = Φ_χ` is a character of `V_{3,r}G_i` for every `r >= 1`,
  and `Φ(t_(α)) = χ(t) = 1`.
- Since `t in (G_i)_0`, we have `t_(α) in Γ_0 = V_{3,r}(G_i)_0 <= Γ_j`. So `Φ|_{Γ_j} != 0` for every level `j`.
- For `r = 1`, `rover-nekrashevych-characters-are-sum-invariant` identifies `Hom(V_3 G_i, R)` with the sum-invariant
  characters. Those are the real span of `χ`, because the system of §3 has rational coefficients. So
  `Hom(V_3 G_i, R) = R Φ`.

∎

*Remark.* The converse of the Lemma also holds for `r >= 2`: every character of `V_{d,r}G` is some `Φ_χ`. The proof is
the one used for `r = 1`:

- real characters vanish on `V_{d,r}`;
- any two proper cones are exchanged by an element of `V_{d,r}`;
- `g_(α) = σ ∏_x (g|_x)_(αx)`, where `σ in V_{d,r}` is the prefix permutation.

This is the `r >= 2` character description that `rover-nekrashevych-bnsr-full-via-type-one-partitions` lacks. The
claim above uses only the direction proved here.
