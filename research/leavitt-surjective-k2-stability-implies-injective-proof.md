---
rg: 2
id: leavitt-surjective-k2-stability-implies-injective-proof
kind: route
title: An explicit unitary agrees with the isometry e on the e-corner, so the twist by e is an automorphism there
target: leavitt-surjective-k2-stability-implies-injective
requires:
  - leavitt-stabilization-kernels-are-one-step
  - leavitt-resolvent-stable-k2-class-is-computable
---

**The unit `u`.** Put `v = f e* f* + e f f* f*`.
- `v* = f e f* + f f f* e*`. Expanding with `e*e = f*f = 1` and `e*f = f*e = 0` gives `v* v = f(ee* + ff*)f* = ff*` and
  `v v* = ff* + e ff* e*`.
- `u = e e e* + v`. Then:
  - `u* u = (e e* e*)(e e e*) + (e e* e*) v + v* (e e e*) + v* v`. The first term is `e e* e e* = e e*`. The cross terms
    vanish: `(e e* e*) v = e e* (e* f) e* f* + e e* f f* f* = 0 + e (e* f) f* f* = 0`, and
    `v* (e e e*) = f e (f* e) e e* + f f (f* e) e* = 0`. So `u* u = ee* + ff* = 1`.
  - `u u* = e e e* e* + v v* = e²e*² + ff* + eff*e*`. Since `e e* = e(ee* + ff*)e* = e²e*² + eff*e*`, this is `ee* + ff* = 1`.
    The cross terms vanish: `(e e e*) v* = e e (e* f)(e f* + f f* e*) = 0` and `v (e e* e*) = (f e* + e f f*)(f* e) e* e* = 0`.
  - So `u` is a unit with `u^-1 = u*`.
- **Agreement with `e`.** `u e e* = e e e* e e* + v e e* = e e e* + (f e* f* e + e f f* f* e) e* = e e e*`, using `f* e = 0`.

**Item 1.**
- On a generator `X_iN(a)` with `a in R ee*`: `Σ^(e)` gives `X_iN(a e*)`, and `Σ^(u)` gives `X_iN(a u*)`. Now
  `a = a ee*`, so `a u* = a ee* u* = a (u e e*)* = a (e e e*)* = a e e* e* = a e*`.
- On `X_Nj(b)` with `b in ee* R`: `Σ^(u)` gives `X_Nj(u b) = X_Nj(u ee* b) = X_Nj(e e e* b) = X_Nj(e b)`, which is `Σ^(e)`.
- Both fix the `X_ij(a)` with `i, j < N`. So `Σ^(e)` and `Σ^(u)` agree on the generators of `H_(ee*)`, hence on
  `H_(ee*)`.
- `Σ^(u)` is an automorphism with inverse `Σ^(u*)` (`leavitt-stabilization-kernels-are-one-step`, item 3). So
  `ker Σ^(e) ∩ H_(ee*) = 1`.
- For `f`, use the unitary `W = ef* + fe*`. `Σ^(W)(H_(ee*)) = H_(W ee* W*) = H_(ff*)`, since `W e = f`. `U_N = ker j_N` is
  `Σ^(W)`-invariant, because `j_N ∘ Σ^(W)` equals the automorphism of `St_(N+1)(R)` for `diag(1, ..., 1, W, 1)`
  composed with `j_N`. So `U_N ∩ H_(ff*) = Σ^(W)(U_N ∩ H_(ee*)) = 1`.

**Item 2.**
- `j_N = D_N Σ^(e)`, and `D_N(K_2(N)) = K_2(N+1)`, since `D_N` is an isomorphism lifting `α_N`.
- If `j_N(K_2(N)) = K_2(N+1)`, then `D_N(Σ^(e)(K_2(N))) = D_N(K_2(N))`, so `Σ^(e)(K_2(N)) = K_2(N)`.
- The image of `Σ^(e)` lies in `H_(ee*)`: `a e* = a e* (ee*)` lies in `R ee*`, and `e b = (ee*) e b` lies in `ee* R`.
- So `U_N ⊆ K_2(N) ⊆ H_(ee*)`, and item 1 gives `U_N = 1`.

**Item 3.**
- `K_2(N, R_L) = U_N · S`: every `x` is `(x s^-1) s` with `s = {ι[x], N+1}_N` and `x s^-1 in U_N`.
- `S` is written with `X_12`, `X_21` only, and `N >= 3`. So every `Σ^(g)` fixes `S` pointwise, and `S ⊆ H_p` for every `p`.
- **The two equalities.**
  - `Σ^(e)(U_N S) = S`, since `Σ^(e)` kills `U_N`.
  - For `x in K_2(N) ∩ H_(ee*)`, item 1 gives `Σ^(u)(x) = Σ^(e)(x) in S`. So `x = Σ^(u*)(s) = s in S`.
- **The equivalences.**
  - `U_N = 1` gives `K_2(N) = S ⊆ H_(ee*)`.
  - `K_2(N) ⊆ H_(ee*)` gives `K_2(N) = S`, hence `U_N = U_N ∩ S = 1`, because `ι` is injective on `S`.
  - Surjective stability gives `U_N = 1` by item 2.
  - `U_N = 1` gives `K_2(N) = S`, and then `j_N(S) = D_N(S) = K_2(N+1)`, since `D_N` fixes `S`.

**Item 4.** This is items 1 and 3 read contrapositively.
