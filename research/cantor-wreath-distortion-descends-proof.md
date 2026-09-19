---
rg: 2
id: cantor-wreath-distortion-descends-proof
kind: route
title: A word of length L in a continuous wreath has, at every point, a fibre value that is a word of length L in finitely many fibre values; a power with torsion base image is a pure fibre element, and evaluating it at a point of infinite order carries the distortion down
target: cantor-wreath-distortion-descends-to-fibre-or-base
requires: []
---

Direct proof. Not independently reviewed. Notation as in `cantor-wreath-distortion-descends-to-fibre-or-base`.

**Step 0 (finite values).** Every `f ∈ C(X,Γ)` takes finitely many values. The sets `f^{-1}(γ)`
form an open cover of the compact space `X`, because `Γ` is discrete. So `F` is finite. It is
symmetric, because `(f,w)^{-1} = (w^{-1}·f^{-1}, w^{-1})`, and the values of `w^{-1}·f^{-1}` are
the inverses of the values of `f`. Since `S = S^{-1}`, `F` contains the values of each `f_{s^{-1}}`.

**Step 1 (value bound).** Let `g = s_1 ⋯ s_L` with `s_i ∈ S`. Then `g = (f,w)` with
`w = w_{s_1}⋯w_{s_L}` and

  `f(x) = f_{s_1}(x) · f_{s_2}(u_1^{-1}x) · ⋯ · f_{s_L}(u_{L-1}^{-1}x)`, where `u_i = w_{s_1}⋯w_{s_i}`.

Proof by induction on `L`. Right multiplication by `s = (f_s,w_s)` gives
`(f,w)(f_s,w_s) = (f·(w·f_s), w w_s)`, and `(w·f_s)(x) = f_s(w^{-1}x) ∈ F`. Consequently:
- `|f(x)|_F ≤ |g|_S` for every `x ∈ X`, where `f(x) ∈ ⟨F⟩`;
- `|π(g)|_{π(S)} ≤ |g|_S`.

**Step 2 (case i).** If `π(g)` has infinite order, then
`|π(g)^N|_{π(S)} = |π(g^N)|_{π(S)} ≤ |g^N|_S = D(N)` by Step 1.

**Step 3 (case ii).**
- Suppose `π(g)` has finite order `p`. Then `g^p = (h, 1)` for some `h ∈ C(X,Γ)`.
- Since `(h,1)^N = (h^N, 1)` with pointwise powers, `g^{pN} = (h^N, 1)`.
- `h` takes finitely many values (Step 0). If all of them had finite order, with `e` the lcm of
  those orders, then `h^e ≡ 1` and `g^{pe} = 1`. That contradicts the infinite order of `g`.
- So choose `x_0` with `γ = h(x_0)` of infinite order.
- Step 1 applied to a geodesic word for `g^{pN}` gives `γ^N = h^N(x_0) ∈ ⟨F⟩` and
  `|γ^N|_F ≤ |g^{pN}|_S = D(pN)`. The case `N = 1` shows `γ ∈ ⟨F⟩`.

This proves the Theorem.

**Corollary 1.**
- Let `g ∈ H` have infinite order, where `H ≤ C(X,Γ) ⋊ W` is finitely generated.
- In case (i), `π(g)` has infinite order in the finitely generated `⟨π(S)⟩ ≤ W`. Since `W` is
  distortion-free, `κN − C ≤ |π(g)^N| ≤ D(N)`.
- In case (ii), `γ` has infinite order in the finitely generated `⟨F⟩ ≤ Γ`. So
  `κ'N − C' ≤ |γ^N|_F ≤ D(pN)`.
- For general `M`, write `M = pN + r` with `0 ≤ r < p`. Then `D(M) ≥ D(pN) − r ≥ κ'N − C' − p`,
  which is linear in `M`.
- A direct product `Γ × W` is `C(pt, Γ) ⋊ W` with the trivial action, so it is covered.

**Corollary 2.**
- Write `H_3 = ⟨a,b⟩`, `c = [a,b]`, and `S = {a^{±1}, b^{±1}}`. Since `c` is central,
  `[a^N, b^N] = c^{N^2}`, so `D(N^2) ≤ 4N`, and more generally `D(q^2N^2) ≤ 4qN`.
- Also, `c` has infinite order.
- In case (i), take `δ = π(c)` and `T = π(S)`. Then `|δ^{N^2}| ≤ D(N^2) ≤ 4N`.
- In case (ii), take `δ = γ^p ∈ ⟨F⟩`, which has infinite order. Then
  `|δ^{N^2}|_F = |γ^{pN^2}|_F ≤ D(p^2N^2) ≤ 4pN`. So `K = 4p` works.

**Corollary 3.**
- Write `BS(1,k) = ⟨s, u | u s u^{-1} = s^k⟩` and `S = {s^{±1}, u^{±1}}`. Then `s` has infinite
  order.
- Also `u^n s^j u^{-n} = s^{j k^n}`, so `D(j k^n) ≤ 2n + |j|`.
- Case (i) gives `|π(s)^{k^n}| ≤ 2n + 1`.
- Case (ii) gives `|γ^{k^n}|_F ≤ D(p k^n) ≤ 2n + p`.
