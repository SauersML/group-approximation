---
rg: 2
id: extendable-edge-hnn-untwisting-proof
kind: route
title: Realize the stable letter as an automorphism letter times a letter centralizing the edge, and check Britton reducedness letter by letter
target: extendable-edge-hnn-embeds-in-identity-hnn-of-mapping-torus
requires: []
---

Standard facts used: Britton's lemma for HNN extensions (Lyndon--Schupp IV.2.1);
free groups have unique roots and cyclic centralizers; the terms `gamma_k` of the
lower central series are characteristic, and in a free group they meet in `1`
(Magnus).

## (i) Untwisting

**The group.** Put `G = A' ⋊_Phi Z = < A', u | u x u^-1 = Phi(x) >`, and let `H`
be the HNN extension of `G` with stable letter `s` over the identity of `C <= G`.
Then `A <= A' <= G <= H`, and `H = G *_C (C × <s>)`.

**Well defined.** Define `iota(a) = a` for `a in A` and `iota(t) = u s`. For
`c in C`,

```text
(u s) c (u s)^-1 = u (s c s^-1) u^-1 = u c u^-1 = Phi(c) = phi(c).
```

So every defining relation of `A*_phi` holds in `H`.

**Injective.** `iota` is injective on `A`. Let

```text
w = a_0 t^{e_1} a_1 t^{e_2} ... t^{e_n} a_n,   n >= 1, e_i = ±1, a_i in A,
```

be Britton-reduced in `A*_phi`:
- no `a_i` with `e_i = 1, e_{i+1} = -1` lies in `C`;
- no `a_i` with `e_i = -1, e_{i+1} = 1` lies in `D`.

Substitute `t = u s` and `t^-1 = s^-1 u^-1`. The image is an `s`-word
`g_0 s^{e_1} g_1 ... s^{e_n} g_n` with every `g_i in G`. For `0 < i < n` the
letter `g_i` is `a_i`, with `u^-1` in front if `e_i = -1` and `u` behind if
`e_{i+1} = 1`. A pinch `s^{e_i} g_i s^{e_{i+1}}` of `H` needs
`e_{i+1} = -e_i` and `g_i in C`.
- If `e_i = 1` and `e_{i+1} = -1`, then `g_i = a_i`, which is not in `C`.
- If `e_i = -1` and `e_{i+1} = 1`, then `g_i = u^-1 a_i u = Phi^-1(a_i)`. It lies in
  `C` exactly when `a_i in Phi(C) = D`, which it does not.

So the image is Britton-reduced with `n >= 1` letters `s`, and by Britton's lemma
in `H` it is nontrivial. Every nontrivial element of `A*_phi` is either in `A` or
a reduced word with `n >= 1`, so `iota` is injective. QED (i).

## (ii) Free factors

Write `F = C * C' = D * D'`. Ranks add under free products, so
`rk C' = rk F - rk C = rk F - rk D = rk D'`. Choose any isomorphism
`theta : C' -> D'`. Then `Phi = phi * theta` is an isomorphism `C * C' -> D * D'`,
that is, an automorphism of `F` with `Phi|_C = phi`. Apply (i) with `A = A' = F`.
QED (ii).

## (iii) Obstructions over free overgroups

Suppose `F <= F'` with `F'` free and `Phi in Aut(F')` with `Phi|_C = phi`.

**Root exponent.** For `1 != x in F'` let `e(x)` be the largest `k` with
`x = y^k`. It is finite, and `x = r^{e(x)}` for a unique root `r`, which is not a
proper power. The centralizer of `x` is `<r>`, so the maximal root of `x^k` is
`r` and `e(x^k) = |k| e(x)`. The exponent `e` is invariant under conjugation and
under `Aut(F')`, so `e(phi(c)) = e(Phi(c)) = e(c)`. If `phi(c)^m` is conjugate to
`c^n`, then

```text
|m| e(c) = |m| e(phi(c)) = e(phi(c)^m) = e(c^n) = |n| e(c),
```

so `|m| = |n|`. This contradicts the hypothesis.

**Depth.** For `1 != x in F'` let `d(x)` be the largest `k` with
`x in gamma_k(F')`. It is finite because the `gamma_k(F')` meet in `1`. It is
`Aut(F')`-invariant because each `gamma_k` is characteristic. Take `c` with
`phi(c) in [N_c, F]`, and put `k = d(c)`.
- `gamma_k(F')` is normal in `F'` and contains `c`, so it contains `N_c`.
- So `[N_c, F] <= [gamma_k(F'), F'] = gamma_{k+1}(F')`, and `d(phi(c)) >= k + 1`.
- But `d(phi(c)) = d(Phi(c)) = d(c) = k`, a contradiction.

For `phi(a) = [a, b]` we have `[a, b] in [N_a, F]`. QED (iii).
