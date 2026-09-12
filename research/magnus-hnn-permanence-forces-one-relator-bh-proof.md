---
rg: 2
id: magnus-hnn-permanence-forces-one-relator-bh-proof
kind: route
title: Induct on relator length through the Magnus--Moldavanskii hierarchy with virtually free groups at the bottom
target: magnus-hnn-permanence-forces-one-relator-boone-higman
requires: [hyperbolic-groups-satisfy-boone-higman, magnus-moldavanskii-hierarchy-with-decidable-edges]
artifacts:
  - research/artifacts/one-relator-boone-higman-2026-09-12.md
---

Write (M) for `bh-embeddability-survives-magnus-subgroup-hnn`, and assume it.
"Embeds" means embeds in a finitely presented simple group. Replacing a relator
by its cyclic reduction does not change the group, so relators are cyclically
reduced and nontrivial. Let `σ_y(w)` be the exponent sum of the letter `y` in
`w`.

**Statement P(n).** For every finite `X` and every relator `r` with `|r| <= n`,
the group `<X | r>` embeds. We prove P(n) by induction on `n`. Fix `G = <X | r>`
with `|r| = n`, and assume P(n-1).

## Step 0: at most one letter occurs

Then `r = x^k` with `k >= 1` (replace `r` by `r^-1` if needed), and
`G = Z/k * F(X \ {x})`. The kernel of the map onto `Z/k` that kills `X \ {x}` is
free by the Kurosh subgroup theorem, so `G` is virtually free. It is therefore
hyperbolic and embeds, by `hyperbolic-groups-satisfy-boone-higman`.

## Step 1: unused letters

Let `X_0` be the set of letters occurring in `r`, with `|X_0| >= 2`, and let
`z ∈ X \ X_0`. Then `G = H * <z> = H*_β` with `H = <X \ {z} | r>`,
`Y_1 = Y_2 = ∅` and stable letter `z`. The empty set omits every letter of `r`,
so (M) passes from `H` to `G`. After `|X \ X_0|` such steps, P for `<X | r>`
follows from P for `<X_0 | r>`, which has the same relator.

From now on every letter of `X` occurs in `r`, and `|X| >= 2`.

## Step 2: some letter has exponent sum zero

**The rewritten relator.** Let `t ∈ X` with `σ_t(r) = 0`, and put `Y = X \ {t}`.
Write

    r = t^(e_0) u_1 t^(e_1) u_2 ... u_l t^(e_l),

with `u_j ∈ Y^±` and `e_j ∈ Z`, and put `ε_j = e_0 + ... + e_(j-1)`. Since
`σ_t(r) = 0`, `r` is freely equal to `∏_j t^(ε_j) u_j t^(-ε_j)`. For `y ∈ Y` let
`y_i` be a letter standing for `t^i y t^-i`, and let `r_1 = ∏_j (u_j)_(ε_j)`,
where `(y^(±1))_i = y_i^(±1)`.

- **Cyclically reduced.** Adjacent letters of `r_1` cancel only if `e_j = 0` and
  `u_(j+1) = u_j^-1`, which would make `r` unreduced. The last and first letters
  cancel only if `u_l = u_1^-1` and `ε_l = ε_1`. That means `e_l = -e_0`, so `r`
  would begin and end with mutually inverse letters.
- **Shorter.** `|r_1| = |r| - Σ|e_j| <= |r| - 2`, since `t` occurs in `r` with
  exponent sum zero.

**The HNN data.** For `y ∈ Y` let `m_y <= M_y` be the least and greatest `i`
with `y_i` occurring in `r_1`. Put

    H   = < y_i  (y ∈ Y, m_y <= i <= M_y) | r_1 >,
    Y_1 = { y_i : m_y <= i < M_y },   Y_2 = { y_i : m_y < i <= M_y },
    β(y_i) = y_(i+1).

`Y_1` omits the letters `y_(M_y)` and `Y_2` omits the letters `y_(m_y)`, and
these occur in `r_1`. By item 1 of
`magnus-moldavanskii-hierarchy-with-decidable-edges`, `β` is an isomorphism
`<Y_1> -> <Y_2>`, so `H*_β` is an HNN extension containing `H`.

**`H*_β ≅ G`.** In `<y_i, t | r_1, t y_i t^-1 = y_(i+1)>` put
`y = t^(-m_y) y_(m_y) t^(m_y)`. The relations give `y_i = t^i y t^-i` for
`m_y <= i <= M_y`. So Tietze moves delete every `y_i`, and `r_1` becomes
`∏_j t^(ε_j) u_j t^(-ε_j)`, which is freely equal to `r`. Hence
`H*_β ≅ <Y, t | r> = G`. This is item 3 of the import, in explicit form.

**Conclusion.** `|r_1| < n`, so `H` embeds by P(n-1). By (M), `G` embeds.

## Step 3: no letter has exponent sum zero

**The amalgam.** Choose distinct `a, b ∈ X`, and put `α = σ_a(r)` and
`γ = σ_b(r)`, both nonzero. By item 1, `<b>` is infinite cyclic, since it omits
`a`. Form the amalgam `G' = G *_(b = x^α) <x>`. It contains `G`. By Tietze moves,

    G' = <X \ {b}, x | r_2>,    r_2 = r(b := x^α).

**Change of basis.** The substitution `a = c x^(-γ)` is a change of free basis,
so `G' = <c, x, X \ {a, b} | r_3>` with `r_3 = r(a := c x^(-γ), b := x^α)`.

**`r_3` is nontrivial.** The words `c x^(-γ)` and `x^α` do not commute, so they
freely generate a free subgroup of `F(c, x)`. Together with `X \ {a, b}` they
freely generate a free subgroup, so the substitution `F(X) -> F(c, x, X \ {a,b})`
is injective and `r_3 != 1`.

**Counting.** `σ_x(r_3) = α·σ_b(r) - γ·σ_a(r) = αγ - γα = 0`, because each
`b^(±1)` contributes `±α` and each `a^(±1)` contributes `∓γ`. Let `r_4` be the
cyclic reduction of `r_3`. Each `a` of `r` contributes
one non-`x` letter `c`, each `b` contributes none, and other letters are
unchanged. So `r_4` has at most `|r| - #_b(r) <= n - 1` letters other than `x`.

**Two cases.**
- **`x` does not occur in `r_4`.** Then `|r_4| <= n - 1`, and `G'` is the
  one-relator group `<c, x, X \ {a,b} | r_4>`, with `x` unused. It embeds by
  P(n-1).
- **`x` occurs in `r_4`.** Since `σ_x(r_4) = 0`, `r_4` also involves another
  letter. Apply Step 1 to the letters not occurring in `r_4`, and then Step 2
  with `t = x`. The base relator produced has length
  `|r_4| - #_x(r_4) <= n - 1`. So the base embeds by P(n-1), and (M) gives the
  embedding of `G'`.

In both cases `G <= G'` embeds.

## Conclusion

Steps 0--3 cover every relator, and P(0) is Step 0. So P(n) holds for all `n`,
and every one-relator group embeds in a finitely presented simple group. `∎`

**Which instances of (M) were used.** Step 2 uses shift data, and Step 1 uses
empty associated subgroups. Nothing else.
