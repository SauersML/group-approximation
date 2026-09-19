---
rg: 2
id: kms-hc1-virtual-vertex-route-is-conjugation-inert-proof
kind: route
title: The top Zassenhaus layer is central, so p-power values are lift-independent and conjugation-invariant; weights of real-root leading forms never sum to zero; the two facts together make T5 on conjugates a restatement of the Cartan half of V_n = W_n
target: kms-hc1-virtual-vertex-route-is-conjugation-inert
requires: [kms-hc1-root-p-powers-die-first-deviation-at-3np, kms-hc1-level-m-edge-tails-have-order-at-most-two]
---

Notation of the claim. Write `G = Gamma^` and `K = ker phi^`. For
`g, h` in `G`, `[g,h] = g^-1 h^-1 g h`.

## 0. Two standard facts

- **(Z1)** `[D_i, D_j] <= D_(i+j)` and `D_i^p <= D_(ip)`. In particular
  `D_(d0)/D_(d0+1)` is central in `G/D_(d0+1)`, because `G = D_1`. Also
  `k^p` lies in `D_(p d0) <= D_(d0+1)` for `k` in `D_(d0)`.
- **(Z2)** `K <= D_(d0)`. By definition of `d0`, `K ∩ D_d <= D_(d+1)` for
  every `d < d0`. Now `K <= D_1` since `phi^` is an isomorphism on
  `G/D_2`, and induction gives `K <= D_(d0)`.
  (This uses only `K ∩ D_d <= D_(d+1)`; the intersection of the `D_d` is
  trivial in `G`, but that is not needed.)

## 1. Proof of (P)

Let `y` be in `I_1` with `y^p = 1`, and let `yt` be a lift.

1. **Value lies in `Kd0`.** `phi^(yt^p) = y^p = 1`, so `yt^p` is in `K`,
   which is in `D_(d0)` by (Z2). Its class in `gr_(d0) G` maps to the class
   of `1` in `(L_p)_(d0)`, so it lies in `Kd0`.
2. **Lift independence.** Another lift is `yt k` with `k` in `K`, and
   `k` is in `D_(d0)`. Modulo `D_(d0+1)`, `k` is central by (Z1), so
   `(yt k)^p = yt^p k^p`. Also `k^p` is in `D_(d0+1)`. So
   `(yt k)^p ≡ yt^p mod D_(d0+1)`.
3. **Conjugation.** Let `g = phi^(gt)`. Then `gt yt gt^-1` lifts
   `g y g^-1`, and `(gt yt gt^-1)^p = gt yt^p gt^-1`. Since `yt^p` is in
   `D_(d0)`, it is central mod `D_(d0+1)` by (Z1). So this equals `yt^p`
   mod `D_(d0+1)`.
4. **Vertices.** For `v` in `U_ab`, `U_bc` or `U_ca` we have `v^p = 1` in
   `Gamma`, hence in `G`. So `v` is a lift of `phi(v)` with `v^p = 1`, and
   `Pi(phi(v)) = 0`. Conjugates follow from step 3, and powers are again
   vertex elements.

## 2. Proof of (L)

1. **Leading forms.** Weight the free pro-p group `F = F(X,Y)` by
   `deg X = deg xb` and `deg Y = deg yb`, and give it the weighted Zassenhaus
   filtration `F_(e)`. Since `x` is in `D_(deg xb)` and `y` is in
   `D_(deg yb)`, the homomorphism `f : X -> x, Y -> y` maps `F_(e)` into
   `D_e` (both filtrations are the fastest restricted N-series with these
   initial conditions). `gr F` is the free restricted Lie algebra on `X, Y`
   (Lazard), and `gr f` is the restricted Lie map with `X -> xb` and
   `Y -> yb`. So if `w` has leading form `P_w` in degree `e`, then `w(x,y)`
   is in `D_e` with class `P_w(xb, yb)`.
2. **Weights.** `deg xb, deg yb < d0`, so `xb` and `yb` are the elements
   `E_beta t^k` and `E_gamma t^l` of `U` in degrees below `d0`, where `U`
   equals `L_p`. `U` is multigraded by letters. The letter multidegree
   `(na, nb, nc)` determines the `sl3`-weight `na alpha1 + nb alpha2 -
   nc theta` and the `t`-degree `nc`, and `(np,np,np)` has weight 0.
   `P_w(xb,yb)` is a sum of brackets and p-powers. Each of its
   multihomogeneous components has weight `n1 beta + n2 gamma` with
   `n1, n2 >= 0` and `n1 + n2 >= 1`. This is never 0, because `beta` and
   `gamma` are roots with `beta != -gamma`, and so linearly independent.
   Hence `P_w(xb,yb)` has no `(np,np,np)` component.
3. **The degree `3np` part of `U`.** By (FD) (given Open 1), the kernel of
   `U_(3np) -> (L_p)_(3np)` is `W_n`, which is pure of multidegree
   `(np,np,np)`. The kernel of `U_(3np) -> gr_(3np) G` is `V_n`, and
   `V_n <= W_n`. So `U_(3np) = C ⊕ W_n`, where `C` is the sum of the other
   multidegrees, and `C` maps injectively into both `gr_(3np) G` and
   `L_p`. By step 2, `P_w(xb,yb)` lies in `C`. So its `W_n`-component is
   0, which is the first bullet.
4. **Automatic vanishing.** If `phi^(w(x,y)) = 1`, the image of
   `P_w(xb,yb)` in `(L_p)_(3np)` is 0. By injectivity on `C`,
   `P_w(xb,yb) = 0` in `U`. So the class of `w(x,y)` in `gr_(3np) G` is 0,
   and `w(x,y)` is in `D_(3np+1)`.
5. **Virtual vertices.** For `x = [c,a]` and `y = [b,c]`, the leading forms
   are root vectors in degree 2, and `beta + gamma` is the root of
   `E31 t^2`. A Heisenberg relator `w` of `<x,y>` has
   `phi^(w(x,y)) = 1`, because the images generate the Heisenberg group
   `<x32(t), x21(t)>` of exponent `p`, with centre `x31(t^2)`, up to the
   signs of the images. By step 4, either `w` has leading degree `3np` and
   `w(x,y)` is in `D_(3np+1)` automatically, or its leading degree is below
   `3np`. In that case `P_w(xb,yb) = 0` already in `L_p`, and the class at
   `3np` depends on `w(x,y)` as an element of `G`, not on `xb, yb`.
   If `e > 3np`, then `w(x,y)` is in `D_(3np+1)` already by step 1.
   - The same holds for p-power relators. Every element of `<x,y>` has
     leading form a combination of root vectors of one degree. That degree
     is not divisible by 3, since root heights are `±1` or `±2` modulo 3.
     So its p-th power has leading degree `p deg` different from `3np`.

## 3. Proof of (B)

1. Take `g = x12(lambda)` with `lambda` in `F_p`, which is in `I_1`.
   Compute
   `(I + lambda E12) E21 (I - lambda E12)
    = (E21 + lambda E11)(I - lambda E12)
    = E21 + lambda (E11 - E22) - lambda^2 E12`.
   So `Ad(g) E21` is nilpotent with Cartan part `lambda h_A`.
2. `exp(E21 t^n) = x21(t^n)` is in `I_1` for `n >= 1`, and
   `g x21(t^n) g^-1 = exp(Ad(g)E21 t^n)` has order `p`.
3. By (P), `Pi(g x21(t^n) g^-1) = Pi(x21(t^n))`. (Bridge_n) evaluates the
   right side as 0 (Cartan part 0) and the left side as `lambda C_nA`. With
   `lambda = 1`, this gives `C_nA in V_n`.
4. The same computation with `g = x23(lambda)` and `E32` gives Cartan part
   `lambda h_B`, so `C_nB in V_n`.
5. **Conjugation by `E(lambda E13)`.** By (P) the group value of any
   conjugate equals that of the unconjugated element. A `lambda`-dependent
   reading therefore requires the bridge, and step 3 already extracts the
   Cartan half from the bridge. For the conjugated virtual centre, with
   `x13(lambda)` acting on `x31(t^2)`, the Cartan part is
   `lambda (h_A + h_B)`, by the same computation:
   `(I + lambda E13) E31 (I - lambda E13) = E31 + lambda (E11 - E33) - lambda^2 E13`.
   This computation is at level 2.
6. **`K_n`.** `Pi` takes values in `Kd0`. Both sides of (Bridge_n) lie in
   `span(C_nA, C_nB) + V_n`, so (B) gives no information on `K_n`.

## 4. Why this is the whole of Route 1

Route 1 has three ingredients:
- the Lie leading forms of virtual relators, which are 0 in `W_n` by (L);
- conjugation, which is invisible at the top layer by (P);
- T5, whose transport to `G` is (Bridge_n) and implies the Cartan half, by
  (B).

The only remaining content is the value at `3np` of `w(x,y)` for relators
of leading degree below `3np`. Substituting `x = [c,a]` and `y = [b,c]`
turns `w(x,y)` into a word in `a, b, c`, and its depth-`3np` value is
computed from the relations of `Gamma` alone: a level-`n` S-pair
computation. That is the computation Route 1 was meant to replace.
