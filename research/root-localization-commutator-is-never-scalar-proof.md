---
rg: 2
id: root-localization-commutator-is-never-scalar-proof
kind: route
title: Right multiplication by u^j moves only the second tower index, so the commutator never touches the extreme columns
target: root-localization-commutator-is-never-scalar
requires: []
artifacts:
  - research/artifacts/sk-coefficients-proposal-2026-09-13.md
---

Direct proof. Notation as in the claim.

**Index rules.**
- `u^i χ_{T^aW} = χ_{T^{a+i}W} u^i`, so left multiplication by `f u^i` sends `E_ab(W)` to `E_{a+i,b}(W')`, where `W' ⊆ W` is the clopen set on which `f∘T^{a+i}` equals 1. Over F_q, `f χ_{T^{a+i}W}` is a combination of such indicators.
- `u^{a-b} f' u^j = (f'∘T^{-(a-b)}) u^{a-b+j}`, so right multiplication by `f' u^j` sends `E_ab(W)` to a combination of `E_{a,b−j}(W'')` with `W'' ⊆ W`.
- `E_ab(W) E_cd(W') = δ_bc E_ad(W ∩ W')`, when the levels `T^aU`, `|a| ≤ m`, are disjoint. That is the hypothesis `U ∩ T^jU = ∅` for `0 < |j| ≤ 2m`.

**Step 1.** Put `X = ghg^{-1} − I = g (s E_ij) g^{-1}` and `Y = h^{-1} − I = −s E_ij`. Then `k = (I+X)(I+Y)`, so `k − I = X + Y + XY`.
- The entries of X are `g_{pi} s (g^{-1})_{jq}`. Left multiplication changes the first index `a ∈ {0, ±1}` of `s = λE_{a0}(W)` by at most w, and right multiplication changes the second index 0 by at most w. So they lie in the span of `E_{a'b'}(·)` with `|a'| ≤ w+1 = m` and `|b'| ≤ w`.
- The entries of Y are `0` or `−λE_{a0}(W)`: second index 0.
- The entries of XY are sums of products `E_{a'b'}(·)·λE_{a0}(W) = λ δ_{b'a} E_{a'0}(·)`: second index 0.

So every entry of `k − I` has second index in `[−w, w]`. This is item 1, and it gives `k − I ∈ M_n(B_m(U))`.

**Step 2.** `B_m(U) ≅ M_{2m+1}(LC(U,F_q))` sends `E_ab(W')` to the matrix unit at `(a,b)` times `χ_{W'}`. With `e` the unit of `B_m(U)`, `k − I = e(k−I)e`. So `k = (1−e)I + eke`, and `eke` corresponds to `κ(x) = I_d + (κ(x) − I_d)` in `LC(U, M_d(F_q))`. By Step 1 the columns of `κ(x) − I_d` indexed by `(p, b)` with `b = ±m` vanish. So `κ(x)` fixes those 2n basis vectors, which is item 2.

**Step 3.** If `κ(x) = λ I_d`, then by item 2 `λ ε_{(1,m)} = ε_{(1,m)}`, so `λ = 1`. This is item 3.

**Consequence for root detection.** Root detection chooses `h` with `[g,h] ≠ 1`, so `κ ≢ I`. By item 3 any `x_0` with `κ(x_0) ≠ I` has a non-scalar value, which is the hypothesis of the non-scalar case. ∎
