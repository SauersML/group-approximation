---
rg: 2
id: compiled-bs-stable-letters-never-rediagonalized-proof
kind: route
title: Every non-base element of the compiled BS(1,m) is conjugate to s^j u^n, whose fresh-coordinate drift has constant sign; transport of codes and the zero-drift lemma finish
target: compiled-bs-stable-letters-are-never-rediagonalized
requires:
  - brick-diagonal-power-conjugacy-forces-zero-drift
  - brick-diagonal-ascending-hnns-embed-in-brin-thompson-groups
---

**Step 1 (conjugacy normal form).** Write `BS(1,m) = Z[1/m] ⋊ ⟨u⟩`, with `u` acting by `×m` and `s`
corresponding to `1 ∈ Z[1/m]`. For `x ∈ Z[1/m]`,
`x · (r u^n) · (-x) = (r + (1 - m^n) x) u^n`.
Since `m` is a unit modulo `m^{|n|} - 1`, `Z[1/m] / (m^{|n|} - 1) Z[1/m] ≅ Z/(m^{|n|}-1)`, with
integer representatives. So every `b = r u^n` with `n ≠ 0` is conjugate inside `⟨s,u⟩` to `s^j u^n` for
an integer `j`.

**Step 2 (transport).** If `c ∈ (k+1+l)V` and `δ_{e'}(b') = b'^{m'}` with `b' = c b c^{-1}`, then the
code `e''_i = c^{-1} e'_i c` satisfies `δ_{e''}(b) = c^{-1} δ_{e'}(b') c = b^{m'}`. The `e''_i` are
brick-local and their images partition the space. So the property "admits a brick-diagonal
power-conjugacy" is invariant under conjugation. It suffices to treat `b = s^j u^n` (times `id` on
the extra coordinates).

**Step 3 (signed drift).** Look at the exponent in the fresh coordinate `k+1`.
- `s^j = T^j × id` does not touch it: that component is `0` pointwise.
- `g` inserts a nonempty code word `c_i` there: `+|c_i| >= +1` pointwise. So `u = g^{-1}` gives `<= -1`.
- By the cocycle rule, `(δ_{s^j u^n})_{k+1} <= -n` pointwise if `n > 0`, and `>= |n|` if `n < 0`.
- Coordinates `k+2, …` are untouched.

**Step 4.** By the pointwise corollary of `brick-diagonal-power-conjugacy-forces-zero-drift`, applied
on `C^{k+1+l}`, `s^j u^n × id` admits no brick-diagonal power-conjugacy. By Step 2, neither does `b`.

**Consequence 2 (chain compiler).** Let `H` be the `δ_{e'}`-closure of `⟨b, c⟩` in `kV`. It is
`δ_{e'}`-closed by construction.
- `brick-diagonal-ascending-hnns-embed-in-brin-thompson-groups` gives `g'` with
  `g'^{-1} (h × id) g' = δ_{e'}(h) × id`.
- Put `a = g'^{-1}`. Then `a (b × id) a^{-1} = b^{m'} × id`.
- `(b × id)(c × id)(b × id)^{-1} = c^m × id` holds because it holds in `kV`.
- `c × id` has infinite order.

**Remark (equal-length codes).** When `m = 2^ℓ` and the code `c_i` consists of all words of length `ℓ`,
every element `t^a h t^{-b}` of any compiled `H *_δ` has fresh-coordinate exponent exactly `ℓ(a-b)`
pointwise. So the conclusion holds for every compiled ascending HNN extension, with no conjugacy
reduction. ∎
