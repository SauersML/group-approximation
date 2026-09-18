---
rg: 2
id: haagerup-splits-as-coset-plus-subgroup-properness-proof
kind: route
title: "Add the two functions and use subadditivity of the square root of a cnd function"
target: haagerup-splits-as-coset-plus-subgroup-properness
requires: []
---

**Fact (subadditivity).** If `ψ = ‖b‖²` for a 1-cocycle `b` of an orthogonal representation
`π`, then `√ψ(gh) ≤ √ψ(g) + √ψ(h)` and `ψ(g^{-1}) = ψ(g)`.
*Proof.* `b(gh) = b(g) + π(g) b(h)`, so `‖b(gh)‖ ≤ ‖b(g)‖ + ‖b(h)‖`. And
`0 = b(e) = b(g) + π(g) b(g^{-1})` gives `‖b(g^{-1})‖ = ‖b(g)‖`. ∎

Schoenberg's theorem (every cnd `ψ` with `ψ(e) = 0` is `‖b‖²` for some cocycle, and conversely)
is standard (Bekka–de la Harpe–Valette, *Kazhdan's property (T)*, Theorem C.2.3); the
statement here can also be read with "cnd function" *defined* as `‖b‖²`, which needs no import.
Sums of cnd functions are cnd (direct sum of the cocycles).

**(1) ⇒ (2).** Take `ψ_1 = ψ_2 = ψ` proper. A finite sublevel set `F_R` lies in the finite union
of cosets `∪_{g ∈ F_R} gH`, and `{h ∈ H : ψ(h) ≤ R} ⊆ F_R` is finite.

**(2) ⇒ (1).** Put `ψ = ψ_1 + ψ_2`, a cnd function. Fix `R`. Since `ψ_1 ≤ ψ`, the sublevel set
`{ψ ≤ R}` lies in `g_1H ∪ ... ∪ g_rH`. Let `M = max_i √ψ_2(g_i)`. If `g = g_i h` with
`ψ(g) ≤ R`, then `h = g_i^{-1} g` and

```text
√ψ_2(h) ≤ √ψ_2(g_i^{-1}) + √ψ_2(g) ≤ M + √R .
```

So `h` lies in the finite set `{h ∈ H : ψ_2(h) ≤ (M + √R)²}`, and `g` in the finite set obtained
by multiplying its elements on the left by `g_1, ..., g_r`. Hence `{ψ ≤ R}` is finite and `ψ` is
proper. ∎

**Remarks.**
- Right cosets give the same notion for cnd functions, since sublevel sets are symmetric.
- For `H` normal and `ψ_1` pulled back from a proper cnd function on `G/H`, this is the familiar
  extension argument; nothing here needs normality.
