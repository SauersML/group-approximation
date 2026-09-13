---
rg: 2
id: bilipschitz-periodic-exponents-vanish-proof
kind: route
title: Periodic Lipschitz exponents are conjugation invariant, homogeneous and bounded, so a proper-power relation that rescales them along conjugator orbits forces them to vanish
target: bilipschitz-proper-power-conjugates-have-zero-periodic-exponents
requires: []
---

Notation is as in the target.

**Item 1 (cocycle).** `ℓ_(gh)(x, y) = ℓ_g(hx, hy) + ℓ_h(x, y)`, by adding and
subtracting `log d(hx, hy)`. Also `|ℓ_h| ≤ C_h`, so `C_(gh) ≤ C_g + C_h`.

**Item 2 (limits exist).** Let `hz = z`.
- If `y → z` with `y ≠ z`, then `h^n y → z` and `h^n y ≠ z`. Since
  `h^n z = z`, Item 1 gives `ℓ_(h^(m+n))(z, y) = ℓ_(h^m)(z, h^n y) + ℓ_(h^n)(z, y)`.
- Taking `liminf` gives `a_(m+n) ≥ a_m + a_n`, and taking `limsup` gives
  `b_(m+n) ≤ b_m + b_n`.
- `|a_m|, |b_m| ≤ C_(h^m) ≤ m C_h`.
- By Fekete's lemma `a_m/m` and `b_m/m` converge, with limits in `[-C_h, C_h]`.

**Item 3 (homogeneity and inverses).**
- For `p ≥ 1`, `a_m(h^p, z) = a_(pm)(h, z)`, so `μ^±(h^p, z) = p μ^±(h, z)`.
  Hence `ν^±_z(g)` does not depend on the period: `pp'` is a period whenever
  `p` and `p'` are.
- `ℓ_(h^-m)(z, y) = -ℓ_(h^m)(z, h^-m y)`. As `y` runs over the punctured
  neighbourhoods of `z`, so does `h^-m y`. So `a_m(h^-1, z) = -b_m(h, z)`, and
  `μ^-(h^-1, z) = -μ^+(h, z)`, `μ^+(h^-1, z) = -μ^-(h, z)`.
- So if `g^p z = z` and `s ≠ 0`:
  - `μ^±(g^(ps), z) = s p ν^±_z(g)` when `s > 0`;
  - `μ^±(g^(ps), z) = -|s| p ν^∓_z(g)` when `s < 0`.
  - With `N_z = max(|ν^+_z(g)|, |ν^-_z(g)|)`, in both cases
    `max(|μ^+(g^(ps), z)|, |μ^-(g^(ps), z)|) = |s| p N_z`.

**Item 4 (conjugation invariance).** Let `hz = z` and `f ∈ G`.
- By Item 1, and since `ℓ_(f^-1)(fz, fy) = -ℓ_f(z, y)`:
  `ℓ_(f h^m f^-1)(fz, fy) = ℓ_(h^m)(z, y) + ℓ_f(z, h^m y) - ℓ_f(z, y)`.
- The error term lies in `[-2C_f, 2C_f]`. As `y → z`, `fy` runs over the
  punctured neighbourhoods of `fz`.
- So `a_m` and `b_m` change by at most `2C_f`, and
  `μ^±(f h f^-1, fz) = μ^±(h, z)`.

**Item 5 (the relation rescales `N`).** Let `g^p z = z`, with `p ≥ 1`.
- `g^(pk) z = z`, so `g^(pl)(fz) = f g^(pk) z = fz`. Item 4 gives
  `μ^±(g^(pl), fz) = μ^±(g^(pk), z)`.
- By Item 3, `|l| p N_(fz) = |k| p N_z`.
- `f^-1 z` is also periodic, since `g^(pk) f^-1 z = f^-1 g^(pl) z = f^-1 z`.
  Applying the same at `f^-1 z` gives `|l| N_z = |k| N_(f^-1 z)`.
- By induction, `N_(f^n z) = (|k|/|l|)^n N_z` for every `n ∈ Z`.

**Item 6 (conclusion).**
- For every periodic `w`, `N_w ≤ C_g`: `|a_m(g^p, w)|, |b_m(g^p, w)| ≤ pm C_g`.
- If `N_z > 0`, take `n → +∞` when `|k| > |l|` and `n → -∞` when `|k| < |l|`.
  Then `N_(f^n z)` is unbounded, a contradiction.
- So `N_z = 0`, that is, `ν^+_z(g) = ν^-_z(g) = 0`.
