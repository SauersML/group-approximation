---
rg: 2
id: dkkms-class-seed-threshold-is-sqrt-l-over-2-to-half-l
kind: claim
title: The class seed law of the folded DKKMS 2-to-1 game has a sharp concentration threshold at beta sqrt(k) of order sqrt(l) 2^(-l/2), with chi-square flatness below and Bernstein identification above, so DKKMS soundness forces beta = O(sqrt(l/(2^l k)) + l/k), a factor 2^(l/2) below the old ceiling, and no seed-guessing labelling can push the ceiling lower
distinct_from:
  dkkms-2to1-value-is-at-least-seed-concentration: that proves val >= 1 - xi - mu_sp and bounds xi by Hoeffding, which gives the ceiling beta = O(sqrt(l/k)); this replaces Hoeffding by Bernstein, which lowers the ceiling to O(sqrt(l/(2^l k)) + l/k), and adds the matching flatness bound, which shows the lowered ceiling is the true threshold of xi up to a constant factor in beta sqrt(k) 2^(l/2)/sqrt(l).
  dkkms-seed-law-is-uniform-in-regime-and-far-in-window: that bounds the per-A-vertex seed law w(R|L) by the covering scale beta sqrt(k) 2^(l+3) and proves the per-tuple law is far from transitive on [k_A, k_T]; this is about the coarser class law w(Q|C) that folding lets a labelling use, whose information scale is beta sqrt(k) 2^(l/2), not beta sqrt(k) 2^l.
  dkkms-2to1-game-sound-at-heavy-smoothing: that is the refuted fixed-rate soundness hole; this locates the exact rate where the refuting mechanism starts and stops.
  near-perfect-selectors-on-rigid-dkkms-instances-put-np-in-rp: that kills selectors below beta sqrt(k) 2^(l+3) <= 10^(-5); this kills soundness above beta sqrt(k) >~ sqrt(l) 2^(-l/2), so between them lies the band where both known tools are provably idle.
artifacts:
  - experiments/dkkms-seed-threshold-2026-09-17/check_seed_threshold.py
---

**ESTABLISHED.** Route: `dkkms-class-seed-threshold-is-sqrt-l-over-2-to-half-l-proof`.

## Setting

The notation is that of `dkkms-2to1-value-is-at-least-seed-concentration`.

- `G(I; l,k,beta)` is the folded DKKMS game (TR16-198 §4.2).
- `w(Q|C)` is the class seed law, with `C = (U, L + H_U)` drawn by edge mass.
- `xi = E_C[1 - max_Q w(Q|C)]`, so `1 - xi = sup_P Pr_edge[P(C) = Q]`, where
  `P` ranges over functions of the class and `Q` is the seed of the edge.

A smoothed block `i` keeps "a variable in the equation `e_i`" (paper, quoted
in `dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`). Let
`nu_i` be the law of that variable. The established nodes read it as
uniform on the three variables. All results below hold for every `nu_i`,
with `s_i := sum_v nu_i(v)^2`, which lies in `[1/3, 1]` and equals `1/3` in the
uniform reading. Put

```text
H      := 2^l - 1                   (hyperplanes of an l-space)
a      := 2^(l-k)
c_i    := beta^2 (2^(l-1) - 1) s_i   (per-block chi-square; uniform: beta^2 (2^(l-1)-1)/3)
chi    := prod_i (1 + c_i) - 1       (<= exp(k beta^2 (2^(l-1) - 1)) - 1 in general)
Delta_l:= 1/2 - 2^(1-l)
```

## Statements

**Theorem F (chi-square flatness of the class seed law).** For every `l >= 2`,
`k >= l + 1`, `beta in [0,1]` and every instance,

```text
1 - xi  <=  M(l,k,beta) / (1 - a)  +  a,
M       :=  min( 1/H + sqrt(chi/H),  2 sqrt((1 + chi)/H) ).
```

So for every class function `P` (every seed-guessing rule, efficient or not),
`Pr_edge[P(C) = Q] <= M/(1-a) + a`.

**Corollary F1 (flat below the threshold).** If `k ln(1 + max_i c_i) <= ln(delta^2 H / 4)`
then `1 - xi <= delta/(1-a) + a`. In the uniform reading it suffices that

```text
k beta^2 (2^(l-1) - 1) / 3  <=  ln(delta^2 (2^l - 1) / 4).
```

In the scaled variable `t := beta sqrt(k) 2^(l/2) / sqrt(l)` this reads
`t^2 <= 6 ln(delta^2 H/4) / l`, which tends to `6 ln 2` (so `t <= 2.03`) as `l`
grows with `delta` fixed.

**Lemma B (Bernstein identification).** Let `l >= 3` and `k >= l + 1`. The
counting rule `P*` of Lemma ID ("the hyperplane of `Lbar` with the most blocks
whose image is at most a line") errs with probability at most
`eps_B/(1-a) + a`, where

```text
eps_B(l,k,beta) = (2^l - 2) exp( - beta^2 Delta_l^2 k / (96 * 2^(-l) + 7 beta / 3) ) + exp(-beta k / 8).
```

Hence `xi <= eps_B/(1-a) + a`. In particular, for `eps in (0,1)`, if

```text
beta >= max( sqrt( 192 ln(2^l/eps) / (Delta_l^2 2^l k) ),  14 ln(2^l/eps) / (3 Delta_l^2 k),  8 ln(1/eps) / k )
```

then `xi <= 2 eps/(1-a) + a`. In the scaled variable the first term is
`t^2 >= 192 ln(2^l/eps) / (Delta_l^2 l)`, which tends to `768 ln 2` (so
`t >= 23.1`).

The old bound `exp(-beta^2 Delta_l^2 k/8)` of Lemma ID charges every kept block
the full Hoeffding range. A kept block has mean-zero score difference with
variance at most `12 * 2^(-l)`, and Bernstein charges it only that.

**Corollary SC' (sharpened smoothing ceiling).** Let `l >= 3` and let `k` be
large enough that `a <= 1/3` and `a + mu_sp(l,k) <= (1-delta)/4`. If the DKKMS
2-to-1 reduction at `(l,k,beta)` has soundness `delta < 1` on even one
triple-simple instance, then, with `Lambda := ln(2^(l+2)/(1-delta))`,

```text
beta  <=  max( sqrt( 192 Lambda / (Delta_l^2 2^l k) ),  14 Lambda / (3 Delta_l^2 k),  8 ln(4/(1-delta)) / k ).
```

So `beta = O( sqrt((l + ln(1/(1-delta))) / (2^l k)) + (l + ln(1/(1-delta)))/k )`.
The old ceiling of Corollary SC was `O(sqrt((l + ln(1/(1-delta)))/k))`. In
`b = beta sqrt(k)` units, the new ceiling is `O(sqrt(l) 2^(-l/2))` once
`k >= l 2^l`, a factor `2^(l/2)` lower.

**Corollary TH (the threshold is sharp).** Fix `delta, eps in (0,1)`, uniform
reading. For all large `l` and all `k >= C(eps) l 2^l`:

- `t <= 2.03 (1 - o(1))` gives `1 - xi <= delta + 3a`, so every seed-guessing
  rule, including the one behind the Theorem LV labelling, matches the edge
  seed with probability `<= delta + 3a`;
- `t >= 23.1 (1 + o(1))` gives `xi <= 3 eps + a`, so by Theorem LV every
  triple-simple instance, NO instances included, has value
  `>= 1 - 3 eps - a - mu_sp`.

So the class seed spread `xi` passes from flat to concentrated inside one
constant factor (at most `12`) of `t`, that is, at `beta sqrt(k) = Theta(sqrt(l) 2^(-l/2))`.
The invariant of the Corollary SC class kill cannot reach below this scale,
and it reaches all the way to it.

**Corollary D (the band where both known tools are idle).** Let `l >= 6`,
`delta in (0,1)` with `2^l >= 8/delta^2 + 1`, uniform reading. Every point with

```text
2^l <= k <= k_T(l) = 4^(l-1)/12,     2/k <= beta <= sqrt( 3 ln(delta^2 H/4) / ((2^(l-1) - 1) k) )
```

(the set is non-empty, since `beta = 2/k` works at `k = 2^l`) has all four
properties:

1. `1 - xi <= delta/(1-a) + a` (Corollary F1), so no seed-guessing labelling
   refutes soundness there;
2. the per-tuple law `P0` is at total variation `>= 1 - e^(-2) - 1/4 > 0.61`
   from every transitive law (Theorem W of
   `dkkms-seed-law-is-uniform-in-regime-and-far-in-window`), so the covering
   step (2) of the outer-honest route loses more than `0.61`;
3. the point is outside regime (R), because `beta sqrt(k) 2^(l+3) >= 64 sqrt(3) > 10^(-5)`,
   so Theorem S does not apply;
4. it contains the published-rate points `beta = ln ln k / k` for every
   `k <= k_T(l)` with `k >= e^(e^2)` and `k >= 2^l (ln ln k)^2`. For large `l`
   this includes the `q = 1` admissible window `[k_A(l), k_T(l)]` of Theorem W,
   where the rigidity half `T2` is open.

So the band holds points of the published construction itself, and neither of
the two recorded tools can be used there: covering (per-tuple scale
`beta sqrt(k) 2^l`) or seed identification (class scale
`beta sqrt(k) 2^(l/2)/sqrt(l)`). Folding hides exactly the seed information
that makes the per-tuple law far from transitive.

## What it changes (impact types 3 and 4)

- **Believed before.** Corollary SC put the soundness ceiling at
  `beta = O(sqrt(l/k))`. The open window between Theorem S and SC was
  `2^(-l)/sqrt(k) <~ beta <~ sqrt(l/k)`.
- **Now.** The ceiling is `beta = O(sqrt(l/(2^l k)) + l/k)` (Corollary SC').
  The window is `2^(-l)/sqrt(k) <~ beta <~ sqrt(l) 2^(-l/2)/sqrt(k)`. Its
  logarithmic length drops from about `l ln 2` to about `(l/2) ln 2`.
- **Class kill, with its limit.** The invariant is the class seed spread `xi`.
  - Every DKKMS-type composition at `t >~ 23` dies at soundness through
    Theorem LV. This covers every route that needs soundness at such a rate,
    and every lift or selector that is built on one.
  - Theorem F proves the invariant is exhausted at `t <~ 2`. No refinement of
    the seed-guessing labelling (MAP seed, lists of one seed per class, any
    efficiency) gets past Corollary TH.
- **Decomposition of the remaining window (Corollary D).** Any decision about
  DKKMS-form H1 instances at `t <~ 2` outside (R) needs a tool that is neither
  per-tuple covering nor class-seed identification. The tool must read the
  per-tuple information that folding removes.

This neither proves nor refutes UGC.

## Checks

`experiments/dkkms-seed-threshold-2026-09-17/check_seed_threshold.py` prints
ALL PASS, in about 4 minutes.

- **(a) Exact enumeration.** For `l = 2..7` it checks the per-block moments
  `E r = 1` and `E r^2 - 1 = beta^2 (2^(l-1)-1)/3`. It also checks the
  kept-block rate `Pr[Z = 1] = 3*2^(1-l) - 2*4^(1-l)`.
- **(b) Monte Carlo on the column model.** At 8 points (`l = 3..6`, `k` up to
  2000) it checks that the Bernstein bound is at most the counting-rule rate,
  which is at most `E max_Q w`, which is at most the flatness bound `M`.
- **(c) The transition in `t`.** At `k = 3000` and `l = 4, 6, 8`, `E max w`
  rises from `0.07, 0.02, 0.01` at `t = 0.1` to `0.99, 1.00, 0.99` at `t = 8`.
  The transition happens at the same `t` for every `l`. In raw
  `beta sqrt(k)` it moves down like `sqrt(l) 2^(-l/2)`: at `l = 8`, `t = 8` is
  `beta sqrt(k) = 1.41`. The old Hoeffding bound is vacuous at every point of
  (c).
- **(d) Constants.** It checks the window condition of Corollary D(4) for
  `20 <= l < 200`, and the constants `2.039`, `23.07`, ratio `11.31` and `0.6147`.

## Attempts

- **2026-09-17, swarm-0917-w19-w19-ugc-last1 (probability-random).** Built as a
  last-mile attack on the DKKMS window between Theorem S and Corollary SC.
  - **Mechanism.** The class sees only `Lbar`. The model density of `Tbar` is a
    product over blocks of `r_i = 1 - beta + beta 2^(l-1) N_i/3`, with mean `1`.
    GL_l-averaging turns `E max_Q w` into `E_ref[max_psi Phi_psi]/H`. The
    second moment of `Phi_psi` is `(1 + c)^k`.
  - **Contrast with the per-tuple law.** The per-tuple density has factor
    `4^(l-1)` instead of `2^(l-1)`, which is why covering fails a factor
    `2^(l/2)` earlier.
  - **What stays open.** The window itself stays open. The obvious next attack
    is an unfolded or list-type labelling at `t <~ 2` that uses the per-tuple
    information.
