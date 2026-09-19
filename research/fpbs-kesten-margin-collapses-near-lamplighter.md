---
rg: 2
id: fpbs-kesten-margin-collapses-near-lamplighter
kind: claim
title: Virtually free quotients converging to the lamplighter have positive but vanishing percolation Kesten margins on the free-group tree, so no local certificate proves the Kesten gap
distinct_from:
  fpbs-percolation-kesten-normal-gap: that asserts the qualitative gap p_c < p_c(N;G) whenever Gamma/N is nonamenable; this proves that the size of the gap is not bounded below by any finite-radius data of the pair, even on one fixed tree with nonamenable virtually free quotients.
  fpbs-tree-normal-relative-threshold-is-inverse-cogrowth: that computes p_c(N;T) for one normal subgroup; this applies it along a marked-group sequence and extracts the collapse of the margin and the local-certificate kill.
  fpbs-direct-limit-certificates-add-no-slack: that shows spectral DT certificates on a direct limit exist iff one finite certificate holds uniformly on the approximants; this concerns the relative threshold along a normal subgroup, with approximants whose quotients are all nonamenable and a limit whose quotient is amenable.
  fpbs-amenable-quotient-normal-relative-threshold-is-pc: that proves no gap when the quotient is amenable; this shows the gap tends to zero as nonamenable quotients approach an amenable one in the marked topology, at the linear rate (q+1)(1-rho_Q)/(q(q-1)).
artifacts:
  - experiments/kesten-margin-collapse-2026-09-17/margin_collapse.py
---

**ESTABLISHED.** Let `T = Cay(F_2, {a^(+-1}, t^(+-1)})`, the 4-regular tree,
so `q = 3` and `p_c(T) = 1/3`. For `n >= 1` put

```text
Q_n = < a, t | a^2, [a, t^k a t^-k]  (1 <= k <= n) >,     N_n = ker(F_2 -> Q_n),
L   = < a, t | a^2, [a, t^k a t^-k]  (k >= 1) >  = Z/2 wr Z,  N_L = ker(F_2 -> L).
```

Write `rho_n` for the spectral radius on `Q_n` of the image `mu_n` of the
uniform measure on `{a, a^-1, t, t^-1}`, and put

```text
s(r) = ( 4r - sqrt(16 r^2 - 12) ) / 6      for r in (sqrt(3)/2, 1],
```

the smaller root of `3 s^2 - 4 r s + 1 = 0`, equivalently of `4s/(1+3s^2) = 1/r`.
Then:

1. **Nonamenable approximants.** Each `Q_n` is virtually free of rank at least
   two, hence nonamenable, and `rho_n < 1`.
2. **Local convergence.** `N_1 <= N_2 <= ...` and `N_L` is their union. For
   `n >= m`, a word of length at most `2m` is trivial in `Q_n` iff it is
   trivial in `L`. So the radius-`m` balls of `Cay(Q_n)` and `Cay(L)` agree
   for `n >= m`.
3. **Positive margins.** For every `n` with `rho_n > sqrt(3)/2`,
   `p_c(N_n;T) = s(rho_n) > 1/3 = p_c(T)`.
4. **Collapse.** `rho_n -> 1`, so

   ```text
   p_c(N_n;T) - p_c(T) = s(rho_n) - 1/3  ->  0,
   s(r) - 1/3 = (2/3)(1 - r) + O((1-r)^2)   as r -> 1.
   ```

   Explicitly, `rho_n >= max_(m <= n) p_(2m)(L)^(1/(2m))`, and the computation
   in the artifact gives `rho_n >= 0.876` and `p_c(N_n;T) - 1/3 <= 0.163` for
   every `n >= 18`.
5. **Limit.** `p_c(N_L;T) = p_c(T) = 1/3`.

**Consequence (class kill).** Call a *local margin certificate* for the Kesten
gap any rule that assigns to a radius `R` and a finite ball `B` a number
`delta(R,B) > 0` such that

```text
p_c(N;G) - p_c(G) >= delta(R,B)
```

for every pair `(G,N)` whose quotient `Gamma/N` is nonamenable and whose
marked quotient graph `Cay(Gamma/N, pi(S))` has radius-`R` ball equal to `B`.
**No local margin certificate exists**, even when it is restricted to pairs on
the single graph `T`. Let `B` be the radius-`R` ball of `Cay(L)`. By item 2,
every `Q_n` with `n >= R` has this ball, and by item 4 their margins tend to
`0`. So `delta(R,B) <= inf_n (s(rho_n) - 1/3) = 0`.

The same data rule out the uniform and transplant forms:

* **No uniform margin near an amenable limit.** Every marked-group
  neighbourhood of `(T, N_L)` contains nonamenable-quotient pairs with
  arbitrarily small margin. So a closed class
  `U_delta = {(G,N) : p_c(N;G) >= p_c(G) + delta}` with fixed `delta > 0`
  never contains a neighbourhood of a nonamenable pair that approximates an
  amenable one. A transplant of the gap through local limits, as in
  `fpbs-l2-gap-class-closed-under-local-limits`, must therefore restrict to a
  spectral compact `K_r = {rho_Q <= r}` with `r < 1`. There the best uniform
  margin is at most `s(r_*) - 1/3`, where `r_* = sup{rho_n : rho_n <= r}`.
  This bound tends to `0` as `r -> 1`.
* **The invariant.** On trees the margin is the function `s(rho_Q) - 1/q` of
  the Kesten spectral radius of the quotient. It is linear in `1 - rho_Q` near
  `rho_Q = 1`. `rho_Q` is only lower semicontinuous in the marked topology
  (item 2 of the proof). Any proof of `fpbs-percolation-kesten-normal-gap`
  must therefore produce a margin that vanishes as the quotient spectral gap
  closes, at least as fast as linearly on trees. It must read `rho_Q` or an
  equally global quantity, and not the ball data of `Gamma/N`.

This is the percolation-Kesten counterpart of the `F_2/F_2^(k) -> F_2` kill of
ball-local `l^q` certificates recorded on
`fpbs-two-point-lq-threshold-gap-universal`. Here, though, the approximants
have nonamenable quotients, and it is the limit quotient that is amenable.

**What it does not do.** It proves no gap and refutes no qualitative gap.
Every `N_n` has a gap. It does not rule out a quantitative Kesten law of the
form `p_c(N;G) - p_c(G) >= F_D(1 - rho_Q)` with `F_D(0+) = 0`, which the tree
data satisfy with `F_D` linear.

**Proof.** `fpbs-kesten-margin-collapses-near-lamplighter-proof`.
