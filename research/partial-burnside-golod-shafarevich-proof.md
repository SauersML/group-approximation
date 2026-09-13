---
rg: 2
id: partial-burnside-golod-shafarevich-proof
kind: route
title: Relators h^N have Zassenhaus degree at least q, and a count of words makes the Golod--Shafarevich series negative at τ = 3/(2m)
target: partial-burnside-presentations-are-golod-shafarevich
requires:
  - golod-shafarevich-presentations-have-infinite-pro-p-completion
  - finite-nilpotent-groups-satisfy-local-restricted-burnside
---

Let `F = F_m` on `X = {x_1, ..., x_m}`, and `S_R = {h^N : h in F, 1 <= |h| <= R}`.
Let `ι: F -> F_p⟨⟨u_1, ..., u_m⟩⟩^×` be the Magnus embedding `x_i -> 1 + u_i`,
`D(f) = deg(ι(f) - 1)`, and `H_{S_R}(t) = Σ_{r in S_R} t^{D(r)}`, as in
`golod-shafarevich-presentations-have-infinite-pro-p-completion`.

**Step 1: degrees.** Let `h in F`. `ι(h)` is a product of the `(1 + u_i)^{±1}`, so
its constant term is `1`, and `v = ι(h) - 1` has no constant term. Write
`N = q·u`.
- In characteristic `p`, `(1 + v)^q = 1 + v^q`: every binomial coefficient
  `C(q, j)` with `0 < j < q` is divisible by `p`, and `v` commutes with itself.
- So `ι(h^N) - 1 = (1 + v^q)^u - 1 = Σ_{j=1}^{u} C(u, j) v^{qj}`. Every term has
  degree `>= q`.
- Hence `D(h^N) >= q` (with `t^∞ = 0` if the series vanished).

**Step 2: count.** `S_R` has at most as many elements as there are reduced words
of length `1, ..., R`:

`|S_R| <= Σ_{ℓ=1}^{R} 2m(2m-1)^{ℓ-1} = (m/(m-1))((2m-1)^R - 1) < 2(2m-1)^R`,

using `m/(m-1) <= 2` for `m >= 2`. For `τ in (0,1)`, Step 1 gives
`H_{S_R}(τ) <= |S_R| τ^q`.

**Step 3: the inequality.** Take `τ = 3/(2m)`, which lies in `(0,1)` for
`m >= 2`, so `1 - mτ = -1/2`. Since `τ < 1` and `q >= 4R + 5`,

`|S_R| τ^q < 2 (2m-1)^R τ^(4R+5) = 2 · [81(2m-1)/(16 m^4)]^R · (3/(2m))^5`.

- `f(m) = (2m-1)/m^4` has derivative `m^{-5}(4 - 6m) < 0` for `m >= 2`, so
  `81 f(m)/16 <= 81·3/256 = 243/256 < 1`, and the bracket to the power `R` is
  `< 1`.
- `(3/(2m))^5 <= (3/4)^5 = 243/1024`.
- So `H_{S_R}(τ) < 2 · 243/1024 = 243/512`, and
  `1 - mτ + H_{S_R}(τ) < -1/2 + 243/512 = -13/512 < 0`.

This is clause 1.

**Step 4: consequences.**
- **Clause 2.** By `golod-shafarevich-presentations-have-infinite-pro-p-completion`,
  the pro-p completion of `Π_R(m,N) = F/⟨⟨S_R⟩⟩` is infinite.
- **Clause 3.** Suppose every finite `p`-group quotient of `Π_R` had order `<= C`.
  A finitely generated group has only finitely many normal subgroups of index
  `<= C`. Their intersection `L_0` has `p`-power index, since `Π_R/L_0` embeds in
  the product of the quotients. Every finite `p`-group quotient then factors
  through `Π_R/L_0`, so the pro-p completion would be `Π_R/L_0`, which is finite.
  That contradicts clause 2. A finite `p`-quotient `Q` of order `> C` is generated
  by the images of the `x_i`, and they satisfy `h^N = 1` for `|h| <= R`.
- **Radius bounds.**
  - Let `R*` witness `LRB(R*, C)`. If `q >= 4R* + 5`, clause 3 at `R = R*`
    gives a finite group of order `> C` satisfying the hypothesis, a
    contradiction. So `R* > (q - 5)/4`.
  - If `q >= 4R_nil + 5`, clause 3 at `R = R_nil` gives finite `p`-groups
    (hence nilpotent) of unbounded order satisfying the law on words of length
    `<= R_nil`. That contradicts clause 1 of
    `finite-nilpotent-groups-satisfy-local-restricted-burnside`, which bounds them
    by `|R(m,N)|`. So `R_nil > (q - 5)/4`. ∎
