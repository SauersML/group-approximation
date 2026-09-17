---
rg: 2
id: higman-order-three-torsion-ratio-bound-proof
kind: route
title: Quantitative Higman smallest-prime collapse with exact telescoping HS estimates
target: higman-order-three-torsion-ratio-bound
requires: []
artifacts:
  - research/artifacts/higman-hs-ratio-scaling-scout-2026-09-17.md
  - experiments/higman-hs-microstate-scaling-2026-09-17/check_torsion_bound.py
---

All norms are the normalized 2-norm `||x||_2=tau(x^*x)^(1/2)` of a trace
`tau` on a von Neumann algebra, and all `g_i` are unitaries. We use three
elementary facts. (F1) `||uxv||_2=||x||_2` for unitaries `u,v`.
(F2) For unitaries `x,y`, `||x^k-y^k||_2<=k||x-y||_2` (telescoping
`x^k-y^k=sum x^(k-1-i)(x-y)y^i`) and `||x^(-1)-y^(-1)||_2=||x-y||_2`.
(F3) `||u x u^(-1)-x||_2<=2||u-1||_2` and
`||u x u^(-1)-v x v^(-1)||_2<=2||u-v||_2`.

Write `a ~_c b` for `||a-b||_2<=c`. Let
`eps_j=||g_j g_(j+1) g_j^(-1)-g_(j+1)^2||_2`. This equals `||r_j-1||_2` by F1.
Also let `tau_i=||g_i^3-1||_2`.

**Step 1: `||g_2^7-1||_2<=7eps_1+2tau_1`, and likewise
`||g_0^7-1||_2<=7eps_3+2tau_3`.**
By F1 and F2, `g_1 g_2^(2^k) g_1^(-1)=(g_1 g_2 g_1^(-1))^(2^k) ~_(2^k eps_1) g_2^(2^(k+1))`.
Conjugating by `g_1` preserves distances (F1). Induction gives
`g_1^3 g_2 g_1^(-3) ~_(eps_1+2eps_1+4eps_1) g_2^8`. By F3,
`g_1^3 g_2 g_1^(-3) ~_(2tau_1) g_2`. Hence
`||g_2^7-1||_2=||g_2^8-g_2||_2<=7eps_1+2tau_1`. The second bound is the
same argument applied to the relation of `r_3` and `g_3`.
Put `s_0=7eps_3+2tau_3`.

**Step 2: `||g_1-1||_2<=eta_1:=9eps_0+10tau_1+14eps_3+4tau_3`.**
We have `g_0 g_1 g_0^(-1) ~_(eps_0) g_1^2`, and `||g_1^2-g_1^(-1)||_2=||g_1^3-1||_2=tau_1` by F1.
So `g_0 g_1 g_0^(-1) ~_(eps_0+tau_1) g_1^(-1)`. Inverting (F2) gives
`g_0 g_1^(-1) g_0^(-1) ~_(eps_0+tau_1) g_1`, and therefore
`g_0^2 g_1 g_0^(-2) = g_0(g_0 g_1 g_0^(-1))g_0^(-1) ~_(eps_0+tau_1) g_0 g_1^(-1) g_0^(-1) ~_(eps_0+tau_1) g_1`.
That is, `g_0^2 g_1 g_0^(-2) ~_(2eps_0+2tau_1) g_1`.
Telescoping four conjugations (F1) gives `g_0^8 g_1 g_0^(-8) ~_(8eps_0+8tau_1) g_1`.
By F3 and Step 1, `g_0^8 g_1 g_0^(-8) ~_(2s_0) g_0 g_1 g_0^(-1)`, since
`||g_0^8-g_0||_2=||g_0^7-1||_2`. Combining with
`g_0 g_1 g_0^(-1) ~_(eps_0+tau_1) g_1^(-1)` gives
`||g_1-g_1^(-1)||_2<=9eps_0+9tau_1+2s_0`. Finally the polynomial identity
`g-1=(g^3-1)-g(g^2-1)` and `||g^2-1||_2=||g-g^(-1)||_2` give
`||g_1-1||_2<=tau_1+||g_1-g_1^(-1)||_2<=eta_1`.

**Step 3: `||g_2-1||_2<=eta_2:=eps_1+2eta_1`.** By F3,
`g_1 g_2 g_1^(-1) ~_(2eta_1) g_2`, and `g_1 g_2 g_1^(-1) ~_(eps_1) g_2^2`. So
`||g_2-1||_2=||g_2^2-g_2||_2<=eps_1+2eta_1`.

**Step 4: `||g_3-1||_2<=eta_3:=eps_2+2eta_2`.** This is the same as Step 3
with `r_2`.

**Step 5: `||g_0-1||_2<=eps_3+2eta_3`.** This is the same as Step 3 with
`r_3`.

Expanding: `eta_1=9eps_0+14eps_3+10tau_1+4tau_3`. Then
`eta_2=eps_1+18eps_0+28eps_3+20tau_1+8tau_3` and
`eta_3=eps_2+2eps_1+36eps_0+56eps_3+40tau_1+16tau_3`. So

```text
||g_0-1||_2 <= 72eps_0+4eps_1+2eps_2+113eps_3+80tau_1+32tau_3.
```

Cauchy--Schwarz gives
`e(g_0)<=(72^2+4^2+2^2+113^2+80^2+32^2)(sum_j eps_j^2+tau_1^2+tau_3^2)`.
That is `e(g_0)<=25397(sum_j e(r_j)+e(g_1^3)+e(g_3^3))`. With `tau_1=tau_3=0`,
the coefficient is `72^2+4^2+2^2+113^2=17973`.

Closure remarks for the claim. `T3` is preserved by direct sums and tensor
products, where the odd generators stay of order three. It is preserved by
tracial ultraproducts, since `g^3=1` is an equation. The bound holds in every
tracial algebra. So these operations cannot produce tuples in `T3` with ratio
above 17973.

The script `check_torsion_bound.py` evaluates every intermediate
inequality on 2639 optimizer and random tuples, all with slack. It is a
sanity check, not part of the proof.
