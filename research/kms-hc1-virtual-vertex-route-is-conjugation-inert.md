---
rg: 2
id: kms-hc1-virtual-vertex-route-is-conjugation-inert
kind: claim
title: At the first deviation of Gamma^A2_p -> I_1 the p-power value of an order-p element is a class function of I_1, and every virtual-vertex word has zero leading-form value on W_n; so the T5 reading of conjugated virtual vertices is circular (its bridge already forces C_nA, C_nB into V_n) and Route 1 gives nothing without the S-pair data
distinct_from:
  kms-hc1-root-p-powers-die-first-deviation-at-3np: that claim reduces the criterion to V_n = W_n for all n >= 2 and proposes virtual-vertex pairs plus T5 as Route 1. This claim proves that Route 1 is inert. Leading forms of virtual words never reach W_n, and the T5 reading is a bridge that already contains the Cartan half of the conclusion.
  kms-hc1-level-m-edge-tails-have-order-at-most-two: that claim proves T5, the p-map of t-homogeneous elements of the Kassel extension N. This claim proves that T5 is not conjugation-invariant while the group-level p-power value is, so T5 cannot be transported to Gamma^.
---

Fix an odd prime `p >= 5` and write `Gamma = Gamma^A2_p`. The map
`phi^ : Gamma^ -> I_1` is the surjection onto the pro-p Iwahori, with
`a -> x12(1)`, `b -> x23(1)` and `c -> x31(t)`.

- `D_d` is the Zassenhaus filtration and `gr I_1 = L_p`.
- `d0` is the first deviation degree: the least `d` such that
  `gr_d Gamma^ -> (L_p)_d` is not injective.
- `Kd0` is the kernel of `gr_(d0) Gamma^ -> (L_p)_(d0)`.
- By (FD) of `kms-hc1-root-p-powers-die-first-deviation-at-3np`
  (conditional on Open 1 there), `d0 = 3np` for some level `n`, and
  `Kd0 = W_n / V_n` sits in multidegree `(np,np,np)`. Here
  `W_n = span(K_n, C_nA, C_nB)`.
- `T5` is the level-`n` Kassel p-map of
  `kms-hc1-level-m-edge-tails-have-order-at-most-two`: in the Kassel
  extension `N`, the `z`-part of `(Y t^n)^[p]` is `alpha(Cart Y)`.

## Statement

> **(P) The p-power value is a class function.** Suppose `d0 < infinity`.
> For `y` in `I_1` with `y^p = 1`, let `Pi(y)` be the class of `yt^p` in
> `gr_(d0) Gamma^`, where `yt` is any lift of `y` to `Gamma^`. Then:
> - `Pi(y)` is well defined and lies in `Kd0`;
> - `Pi(g y g^-1) = Pi(y)` for every `g` in `I_1`;
> - `Pi` vanishes on every `I_1`-conjugate of an element of a vertex group
>   `phi(U_ab)`, `phi(U_bc)` or `phi(U_ca)`, and on all their powers.

> **(L) Virtual words are leading-form inert.** Assume (FD). Let `x, y` be
> in `Gamma^` with leading forms `xb = E_beta t^k` and `yb = E_gamma t^l`,
> which are real-root vectors of `L_p` (in `U`) with `beta != -gamma`.
> Let `w` be a word in the free pro-p group `F(X,Y)`, weighted by
> `deg X = deg xb` and `deg Y = deg yb`, with leading form `P_w` of weighted
> degree `e`. Then:
> - if `e = 3np`, the element `w(x,y)` lies in `D_(3np)`, and its
>   `W_n`-component is 0;
> - if in addition `phi^(w(x,y)) = 1`, then `w(x,y)` lies in `D_(3np+1)`.
>
> So every Heisenberg relator of a virtual vertex, such as `<[c,a],[b,c]>`
> with centre `x31(t^2)`, is either automatically satisfied modulo
> `D_(3np+1)` or has leading degree `e < 3np`. In the second case its value
> at `3np` is not a function of `xb, yb` at all.

> **(B) The T5 bridge is the Cartan half of the conclusion.** Let
> (Bridge_n) be the statement: for every nilpotent `Y` in `sl3(F_p)` with
> `exp(Y t^n)` in `I_1`,
> `Pi(exp(Y t^n)) = cA C_nA + cB C_nB mod V_n`,
> where `Cart Y = cA h_A + cB h_B`. Here `h_A = E11 - E22` and
> `h_B = E22 - E33`, and the signs of `C_nA, C_nB` are those of `alpha` in
> T5. Then (Bridge_n) implies
> `C_nA, C_nB in V_n`. The reason is that `exp(E21 t^n)` and its conjugate
> by `x12(lambda)` have the same `Pi`, by (P). But their Cartan parts are
> `0` and `lambda h_A`, and similarly for `E32` and `x23(lambda)`. Hence:
> - conjugation by `E(lambda E13)`, or by any element of `Gamma^`, can
>   produce no `lambda`-dependent value;
> - reading `alpha_A + alpha_B` off T5 on a conjugated virtual centre
>   presupposes (Bridge_n), which already contains `C_nA, C_nB in V_n`;
> - `K_n` is not reached by (B) at all.

## Consequence for the target

Route 1 of `kms-hc1-root-p-powers-die-first-deviation-at-3np` is inert.
- Its Lie-level content is empty by (L).
- Its T5 step is circular by (B).
- What remains of it is the value of a virtual relator of leading degree
  `e < 3np`. Rewritten in `a, b, c`, this is an ordinary relator of `Gamma`
  at depth `3np`: exactly the level-`n` S-pair data that Route 1 was meant
  to avoid.

The obstruction does not touch Route 2 (group-level Cartan p-powers). By
(P), the `lambda`-linear part of (Bridge_n) for the single pair
`x21(t^n)`, `x12(lambda) x21(t^n) x12(-lambda)` says exactly
`lambda C_nA in V_n`. So a proof of any form of the bridge is a proof of the
Cartan half itself; nothing is gained by passing through T5. The routes
that remain are:
- Route 2;
- the level-`n` S-pairs, as in the nine slices of the edge-tails claim;
- the Kassel line `K_n` by its own argument, since neither (P) nor (B)
  sees it.

## Status

ESTABLISHED as a paper proof, every `p >= 5`, for (P) and (B). (L) is
ESTABLISHED given (FD), that is, given Open 1. No computation is used.
Proof: `kms-hc1-virtual-vertex-route-is-conjugation-inert-proof`.
