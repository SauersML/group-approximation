---
rg: 2
id: contracting-positive-degree-base-nontrivial-characters
kind: claim
title: Contracting self-similar groups of activity degree 1 and 2 whose Rover-Nekrashevych groups carry characters nonzero on the bottom of the activity tower
distinct_from:
  rover-nekrashevych-polynomial-activity-tower-sigma-full: that proves full Sigma-invariants along the activity tower Gamma_0 <= ... <= Gamma_n and needs a separate Meinert branch for characters nonzero on the lower level; this shows that branch is not vacuous, with explicit degree 1 and 2 groups whose characters are nonzero on Gamma_0.
  rover-nekrashevych-characters-are-sum-invariant: that describes Hom(V_d G, R) for all self-similar G; this exhibits new contracting groups of positive activity degree where the description is nonzero, and extends the character construction to every r.
  sum-invariant-characters-of-contracting-groups-via-nucleus: that is the general algorithm; this is its application to two explicit groups.
---

**ESTABLISHED (proof in `contracting-positive-degree-base-nontrivial-characters-proof`; unreviewed;
exact computer certificate plus hand checks).**

Take `X = {0, 1, 2}` and write `g = (g|_0, g|_1, g|_2)π`, meaning `g(xw) = π(x) g|_x(w)`. Define:

    t = (1, 1, t)(0 1 2)          (ternary odometer: ξ ↦ ξ + 1 on Z_3, least significant digit first)
    a = (a, t, t^{-1})(1 2)
    b = (a, b, a)(0 2)

Put `G_1 = ⟨t, a⟩` and `G_2 = ⟨t, a, b⟩`.

**Theorem.**

1. **Contraction and activity.**
   - `G_1` and `G_2` are contracting, with nuclei of size 7 and 8.
   - `θ_k(t) = 1`, `θ_k(a) = 2k + 1` and `θ_k(b) = 2k^2 + 1`.
   - So `G_1` has polynomial activity of degree exactly 1, and `G_2` of degree exactly 2.
2. **Characters.** For `i = 1, 2` the space of sum-invariant characters of `G_i` is one-dimensional. It is spanned by
   the `t`-exponent sum `χ`, with `χ(t) = 1` and `χ(a) = χ(b) = 0`. In particular, `χ` is a well-defined homomorphism
   on `G_i`.
3. **Characters of the Röver–Nekrashevych groups.** For every `r >= 1`, the group `Γ = V_{3,r}G_i` has a character
   `Φ` with `Φ(g_(α)) = χ(g)` for every cone `α` and every `g in G_i`.
   - Since `t` has degree 0, `t_(α)` lies in the bottom `Γ_0 = V_{3,r}(G_i)_0` of the activity tower of
     `rover-nekrashevych-polynomial-activity-tower-sigma-full`.
   - `Φ(t_(α)) = 1`. So `Φ` is nonzero on `Γ_0`, and therefore on every level `Γ_0 <= Γ_1 (<= Γ_2)`.
   - For `r = 1`, `Hom(V_3 G_i, R) = R Φ` by `rover-nekrashevych-characters-are-sum-invariant`.

**Consequence: the base-nontrivial case occurs.**

- In the tower proof, a character of `Γ_{j+1}` either vanishes on `Γ_j`, which is the germ-charge branch, or it does
  not, which is the Meinert/point-fixer branch.
- For `G_1` the character `Φ` is nonzero on `Γ_0`. For `G_2` it is nonzero on `Γ_0` and on `Γ_1`, so its restriction to `Γ_1` is again base-nontrivial.
- So the Meinert branch is used at every step of the tower, and cannot be removed by an argument that only treats
  characters vanishing on the base.
- In the degree-0 (bounded) case the character sphere can already be nonempty, as for the odometer. That sphere lies
  on `Γ_0` itself. What is new here is positive degree with the character living on the base.

**Explicit nucleus of `G_2`.** It contains the nucleus of `G_1`, and the character values are the `t`-exponent sums:

| Element | Recursion | `χ` |
|---|---|---|
| `t` | `(1, 1, t)(0 1 2)` | 1 |
| `t^{-1}` | `(t^{-1}, 1, 1)(0 2 1)` | −1 |
| `a` | `(a, t, t^{-1})(1 2)` | 0 |
| `at` | `(t, t^{-1}, at)(0 2)` | 1 |
| `t^{-1}a` | `(t^{-1}a, t, t^{-1})(0 2)` | −1 |
| `t^{-1}at` | `(t, t^{-1}, t^{-1}at)(0 1)` | 0 |
| `b` | `(a, b, a)(0 2)` | 0 (`G_2` only) |

**Certificate.**

- Script: `experiments/contracting-polynomial-activity-2026-09-17/verify_example.py`. Output: `verify_example.out`.
- As an independent check, no relation among reduced words violates `χ`:
  - `G_1`, words of length `<= 16`: 196606 words, 183168 distinct elements.
  - `G_2`, words of length `<= 10`: 118097 words.
- In `G_1` the first coincidences among reduced words occur at length 11, for example
  `t^3 a t^2 a t^2 a t^{-1} = a t^5 a t^{-1} a t^2`. Both sides have `t`-exponent sum 6.

## Attempts

- The naive tower `a_j = (a_j, a_{j−1}, a_{j−1}^{-1})(1 2)` has no nucleus of size `<= 400` at `j = 2`. Here
  `a_1 a_2` has root permutation 1 and section `a_1 a_2` at the letter 0.
- Moving the fixed letter to 1 gives `b`, which is contracting. Continuing the rotation to degree 3
  (`experiments/contracting-polynomial-activity-2026-09-17/tower2.py`) found no nucleus of size `<= 400`.
- So examples of every degree `n` are still open. Degrees 1 and 2 suffice to show that the Meinert branch is needed.
