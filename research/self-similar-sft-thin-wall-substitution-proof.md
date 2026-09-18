---
rg: 2
id: self-similar-sft-thin-wall-substitution-proof
kind: route
title: Substitute the two configurations instead of an operator family; a width-one wall becomes a wall of width N^m, and the two-dimensional wall certificate refutes every scale
target: self-similar-sft-thin-walls-refute-quantum-rigidity
requires:
  - sft-crossed-product-fp-iff-quantum-rigid
---

Notation is as in the target. `|·|` is the ℓ¹ norm, and (Q1)–(Q3) are as in `sft-crossed-product-fp-iff-quantum-rigid`.

## Wall certificate (recalled, with the width made explicit)

Let `x, y ∈ Ω` agree on the columns `[a, b]`, with `b − a + 1 >= 2D`. Suppose they differ at a site of `L = {i < a}`
and at a site of `R = {i > b}`. Put `W = k^2`, and let `g = [[1,1],[0,1]]`.
- **The family.**
  - For `z ∈ L` or on the wall: `E_c(z) = diag([x(z)=c], [y(z)=c])`.
  - For `z ∈ R`: `E_c(z) = g diag([x(z)=c], [y(z)=c]) g^(-1)`.
  - On the wall `x = y`, so both formulas give `[x(z)=c] I`.
- **(Q1)** holds.
- **(Q2).** Two sites within distance `2D` cannot lie in `L` and `R` respectively, since their distance is at least
  `b − a + 2 > 2D`. So they are simultaneously diagonal in one basis.
- **(Q3).** A ball `B_D` spans `2D + 1 <= b − a + 2` columns, so it misses `L` or `R`. There the product of a pattern `π`
  is `diag([x = π], [y = π])` in one basis, which is `0` when `π` does not occur in `Ω`.
- **Non-commutation.** Take `z_L ∈ L` with `x(z_L) ≠ y(z_L)` and `z_R ∈ R` likewise. Then `E_(x(z_L))(z_L) = diag(1,0)`
  and `E_(x(z_R))(z_R) = g diag(1,0) g^(-1) = [[1,−1],[0,0]]`. These do not commute over any field.

So `Ω` is not `D`-rigid. No gluing of the two configurations is used.

## Item 1

- **One substitution step.** If `x, y ∈ Ω` agree on the columns `[a, b]` and differ in `L` and in `R`, then
  `σ(x), σ(y) ∈ Ω` agree on the columns `[Na, Nb + N − 1]`, which is `N(b − a + 1)` columns.
- **Differences survive.** A difference at a macro site `Z` with `Z_1 < a` makes the blocks `σ(x_Z) ≠ σ(y_Z)` differ, by
  injectivity. That block lies in the columns `< Na`. The right side is the same.
- **Iterate.** From width `1`, `σ^m` gives width `N^m`. Given `D`, choose `N^m >= 2D` and apply the certificate.
  Finite presentation fails by `sft-crossed-product-fp-iff-quantum-rigid`.
- **Rows** are the same.

**A primitive direction `ν`.** Put `ν_+ = Σ max(ν_i, 0)` and `ν_− = Σ max(−ν_i, 0)`.
- For `t = NZ + u` with `u ∈ [0,N)^2`, `⟨Z, ν⟩ = (⟨t, ν⟩ − ⟨u, ν⟩)/N` and `−(N−1)ν_− <= ⟨u, ν⟩ <= (N−1)ν_+`.
- So agreement on `{a <= ⟨Z,ν⟩ <= b}` gives agreement on `{Na + (N−1)ν_+ <= ⟨t,ν⟩ <= Nb − (N−1)ν_−}`.
- In level counts, `w ↦ w' = N(w − 1) − (N−1)|ν|_1 + 1`, so `w' − w = (N−1)(w − 1 − |ν|_1) >= N − 1` once
  `w >= |ν|_1 + 2`.
- Differences stay strictly outside: `N(a−1) + (N−1)ν_+ < Na + (N−1)ν_+`.
- The certificate transfers because `|⟨t − s, ν⟩| <= |t − s|_1 |ν|_∞`. A strip of `w` levels separates the two sides by
  ℓ¹ distance at least `(w+1)/|ν|_∞`, and a ball `B_D` spans at most `2D|ν|_∞ + 1` levels.
- Width growing without bound therefore refutes every `D`.

## Item 2

Let `x, y, u, v` all have column `C` at `0`, with `x_L ≠ y_L` and `u_R ≠ v_R`, where `L = {i < 0}` and `R = {i > 0}`.
- By item 1, any two of them agree on `L` or on `R`. So `x_R = y_R` and `u_L = v_L`.
- Since `u_R ≠ v_R`, the right half `x_R` differs from one of them; say `x_R ≠ u_R`, the other case being symmetric.
  Then `x_L = u_L`.
- Also `y_R = x_R ≠ u_R`, so `y_L = u_L = x_L`. This contradicts `x_L ≠ y_L`.

So either all extensions of `C` agree on `L`, or all agree on `R`. Rows and strips are the same.

## Item 3

**Choice of the pair.** Take `x_1 ∈ Ω` and put `y_1(i,j) = x_1(i, j+1)`.
- **Claim.** `x_1` and `y_1` differ at some column `< 0` and at some column `> 0`.
- Suppose instead that `x_1 = y_1` on the columns `> 0`. Then the horizontal translates `x_1(· + m, ·)` are
  `e_2`-periodic on the columns `> −m`.
- A limit point as `m → ∞` lies in `Ω` and has period `e_2`, which is excluded.
- The left side is the same.

**Agreement.** If the column `i` of `σ(c)` equals a fixed `γ` for every `c`, then `σ(x_1)` and `σ(y_1)` both have
column `i` equal to `γ` stacked. So they agree on that column. They differ at columns `< i` and `> i`, since the
macro-level differences at columns `< 0` and `> 0` survive by injectivity. Item 1 applies.

**The `~_i` version.** The same argument works for any `x_1, y_1 ∈ Ω` with `x_1(0,J) ~_i y_1(0,J)` for all `J` and
differences at macro columns `< 0` and `> 0`.

## Item 4 (Ledrappier)

`x(i,j) + x(i+1,j) + x(i,j+1) = 0` over `F_2`.
- **The substitution.** With `y = (1 + u^(-1) + v^(-1)) x^((2))`, where `x^((2))` is `x` placed on `2Z^2` and `0`
  elsewhere, we get
  `y(2i,2j) = y(2i−1,2j) = y(2i,2j−1) = x(i,j)` and `y(2i−1,2j−1) = 0`.
- **The rule holds again**, checked at the four positions of a block:
  - `0 + a + a = 0`;
  - `a + 0 + a = 0`;
  - `a + a + 0 = 0`;
  - `x(i,j) + x(i+1,j) + x(i,j+1) = 0`.
  So `σ(Ω) ⊆ Ω`, and `σ` is injective.
- **One-sided columns.** `x(i+1,j) = x(i,j) + x(i,j+1)` shows that a column determines the right half-plane. ∎
