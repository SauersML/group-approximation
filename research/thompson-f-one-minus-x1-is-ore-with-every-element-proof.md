---
rg: 2
id: thompson-f-one-minus-x1-is-ore-with-every-element-proof
kind: route
title: Conjugates of x_1 have nested supports (p, 1); apply the x_0 theorem inside F_[p,1], innermost first
target: thompson-f-one-minus-x1-is-ore-with-every-element
requires: [thompson-f-one-minus-x0-is-ore-with-every-element, thompson-f-binomial-pairs-have-common-multiples]
---

Notation as in the target. `F` acts on `[0,1]` by the standard PL maps. `F_[p,1]` is the
subgroup of elements that are the identity on `[0, p]`, for dyadic `p` in `[0, 1)`. `R` is
a domain because `F` is left-orderable.

**Step 0. Supports.**
- `x_0` has support `(0, 1)`: it is `t/2`, `t - 1/4`, `2t - 1` on `[0,1/2]`, `[1/2,3/4]`,
  `[3/4,1]`, with no interior fixed point.
- `x_1` is the identity on `[0, 1/2]` and `t/2 + 1/4`, `t - 1/8`, `2t - 1` on
  `[1/2,3/4]`, `[3/4,7/8]`, `[7/8,1]`, so its support is `(1/2, 1)`.
- Conjugation by `t` in `F` maps supports by `t^-1` and fixes `0` and `1`. So every `g` in
  the conjugacy class of `x_0^{+-1}` has support `(0, 1)`, and every `g` in the class of
  `x_1^{+-1}` has support `(p_g, 1)` with `p_g = t^-1(1/2)` dyadic.
- Write `p_g = 0` in the first case. In both cases `g` lies in `F_[p_g, 1]`.

**Step 1. Each `g` is an `x_0` of its own interval.** There is a group isomorphism
`psi_g : F_[p_g,1] -> F` with `psi_g(g) = x_0^{+-1}`.
- *`g = t^-1 x_0^{+-1} t`.* Take `psi_g(f) = t f t^-1`.
- *`g = t^-1 x_1^{+-1} t`.* Conjugation by `t` maps `F_[p_g,1]` onto `F_[1/2,1]`, because
  `t` maps `[0, p_g]` onto `[0, 1/2]`, and it sends `g` to `x_1^{+-1}`. Then the affine
  rescaling `rho(y) = 2y - 1` gives `rho F_[1/2,1] rho^-1 = F` with
  `rho x_1 rho^-1 = x_0`. For example, on `[1/2,3/4]`, `x_1((y+1)/2) = (y+2)/4` and
  `rho` of that is `y/2`.
- *Consequence.* `psi_g` induces a ring isomorphism `K[F_[p_g,1]] -> K[F]`, and
  `(1 - x_0^-1) K[F] = (1 - x_0) K[F]`. So
  `thompson-f-one-minus-x0-is-ore-with-every-element` transfers: for every nonzero `w` in
  `K[F_[p_g,1]]` there is a nonzero `y` in
  `(1 - g) K[F_[p_g,1]] ∩ w K[F_[p_g,1]]`.

**Step 2. Induction (item 1).** Order the family so that `p_1 <= p_2 <= ... <= p_m`, where
`p_i = p_(g_i)`. Write `R_j = K[F_[p_j,1]]`. For `i >= j`, `g_i` has support in
`(p_i, 1) ⊆ (p_j, 1)`, so `g_i` lies in `F_[p_j,1]`, and `R_(j+1) ⊆ R_j`.

Claim `P(j)`: `∩_(i >= j) (1 - g_i) R_j ≠ 0`.
- `P(m)` holds: `1 - g_m ≠ 0`.
- *`P(j+1)` implies `P(j)`.* Take a nonzero `w` in `∩_(i >= j+1) (1 - g_i) R_(j+1)`.
  Then `w` lies in `R_j`, and for `i >= j+1` it lies in `(1 - g_i) R_j`. By Step 1
  applied to `g_j`, there is a nonzero `y = w z` with `z` in `R_j` and `y` in
  `(1 - g_j) R_j`. Right ideals absorb `z`, so `y` also lies in `(1 - g_i) R_j` for
  `i >= j+1`. Hence `y` is a nonzero element of `∩_(i >= j) (1 - g_i) R_j`.

`P(1)` gives a nonzero element of `∩_i (1 - g_i) R_1 ⊆ ∩_i (1 - g_i) R`.

**Step 3. Item 2.** Let `h` be in `C_+` and `b ≠ 0`.
- For `t` in `supp b`, `g_t = t^-1 h t` lies in `C_+`. Step 2 gives a nonzero `v` in
  `∩_(t in supp b) (1 - g_t) R`.
- By item 2 of `thompson-f-binomial-pairs-have-common-multiples`
  (`t (1 - t^-1 h t) = (1 - h) t`), `b v` lies in `(1 - h) R`.
- `b v ≠ 0` because `R` is a domain. So `b v` is a nonzero element of
  `(1 - h) R ∩ b R`.

**Step 4. Mirror form.** Let `alpha` be the automorphism `x_0 -> x_0^-1`,
`x_1 -> x_1 x_0^-1` (survey arXiv:2305.07113, §1.5, quoted). It induces a ring
automorphism of `R` preserving principal right ideals and augmentation binomials. It maps
conjugacy classes to conjugacy classes: `x_0^{+-1}` to `x_0^{-+1}`, and `x_1^{+-1}` to
`(x_1 x_0^-1)^{+-1}`. So items 1 and 2 transfer.

**Trust surfaces.**
- Quoted: survey Theorem 3.18 (via the required claim), the PL formulas for `x_0` and
  `x_1`, left-orderability of `F`, and that `alpha` is an automorphism (survey §1.5).
- The isomorphism `F_[1/2,1] ≅ F` by affine rescaling is standard and checked on
  generators above.
- Everything else is proved above.
