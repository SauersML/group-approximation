---
rg: 2
id: dilation-letters-cannot-divide-the-unit-class-proof
kind: route
title: Solve the harmonic recursion for the top level and bound the denominators by det M_top
target: dilation-letters-cannot-divide-the-unit-class
requires:
  - single-register-rings-divide-unit-at-finitely-many-primes
---

**Part 1.** Write `h(x) = a/D^m` with `a ≠ 0`. If `x = q y`, then `a/D^m = q h(y) = q b/D^(m')`, so
`q | a D^(m'−m)`. When `q ∤ D`, this forces `q | a`, which happens for only finitely many `q`. ∎

**Part 2.**
- **K_0(B⁺).** As in part 2 of `single-register-rings-divide-unit-at-finitely-many-primes-proof`, `K_0(B⁺)` is
  `⊕_types LC(N ∪ ∞, Z)`, whatever the resolvents. It is free on the point classes `V_(τ,k)` and the tail classes
  `X_τ`. Under (P), `K_0(R) = coker(1 − [X])`, and `Hom(K_0(R), Q)` is the set of *harmonic* functionals: those
  `h` on `K_0(B⁺)` with `h ∘ (1 − [X]) = 0`.
- **The relation at `V_(τ,k)`.** Harmonicity reads `h(V_(τ,k)) = Σ_targets h(target)`. The targets are:
  - points at levels `k + i` with `−(large) <= i <= c`, where dilations contribute only levels `(k − r)/p < k`
    once `k` is large;
  - tail classes, from resets.
- **Recursion.** For `k` beyond a fixed `K`, the coefficients of the levels `k, ..., k+c` are eventually
  constant, and the coefficient of level `k + c` is the matrix `M_top`. If `det M_top ≠ 0`, the harmonicity
  equations at level `k` determine the vector `h(V_(·,k+c))` from:
  - the values at levels `< k + c`;
  - the finitely many tail values;

  with denominators dividing `det M_top`.
- **Consequence.** Every harmonic `h` is determined by finitely many initial values: the levels `< K + c` and the
  tails. It takes values in `Z[1/D]`, with `D = det M_top` times a common denominator of those initial values.
- **Detecting `[1]`.** If `[1] = Σ_τ X_τ` has infinite order, some harmonic `h` has `h([1]) ≠ 0`, since `Q` is
  injective and `Z[1] ⊆ K_0(R)` maps to `Q`. Part 1 then shows that `[1]` is divisible by only finitely many
  primes. ∎

**Dilations with all residues.** The class `X_τ` is sent by each fully available letter to a full tail class. So
`X = f X`, where `f` counts the fully available letters. With `p` residues and `p >= 2`, `(1 − f) X = 0` and `[1]`
is torsion.
