---
rg: 2
id: constant-bias-selectors-break-planted-3lin-proof
kind: route
title: Run the first half of Corollary D's proof with P = RU-YES, which gives (RU-YES minus finitely many, NO) in RP from (P2^RU) and sel without using hardness; then Corollary PR turns any one-sided algorithm for (RU-YES, NO) into a planted-versus-random distinguisher for regular sparse 3LIN
target: constant-bias-dkkms-selectors-break-planted-sparse-3lin
requires:
  - dkkms-orientations-admit-star-lists-on-robustly-unique-inputs
  - planted-regular-3lin-inputs-are-robustly-unique
  - selector-witness-hypotheses-collapse-to-selector-free-form
  - value-free-star-list-references-put-np-in-rp
---

## Step 1: the class and the structure statement

Let RU-YES be the class of the target at radius `rho` and dimension `r0`.
By (P2^RU) (`dkkms-orientations-admit-star-lists-on-robustly-unique-inputs`),
`F_inf(SL^C, RU-YES)` holds. Let `E_0` be its finite set of exceptions and
`P_0 := RU-YES minus E_0`.

## Step 2: the RP algorithm, without hardness

Assume `sel`, and let `S` be a constant-bias selector. By definition it
works on every YES input of regular Gap3Lin, so in particular on every
input of `P_0`. The proof of Corollary D in
`selector-witness-hypotheses-collapse-to-selector-free-form-proof` reads,
verbatim:

> Assume `F_inf(SL^C, P)`, and let `S` be a constant-bias selector. Let `E_0` be
> the finite set of exceptions, and put `P_0 := P minus E_0`. By the first half
> of Theorem X, applied to `P_0`, `Pr[SL^C(x, S(x))] >= theta(|x|)` on every
> `x in P_0`.
>
> This is the hypothesis of Theorem CLV (`value-free-star-list-references-put-np-in-rp`)
> for the promise problem `Lang_0 := (P_0, NO)`. Its instance hypotheses (E_tau),
> (M), (Bw), (M_B) and (S^C_L) are conditions on the instances `D(x)` for YES
> and NO inputs, so they pass to the sub-promise. Theorem CLV gives
> `Lang_0 in RP`.

None of these sentences uses the NP-hardness hypothesis of Corollary D, which
enters only in the next paragraph of that proof (the Karp-reduction
composition). With `P := RU-YES`, we get `(P_0, NO) in RP`. The instance
hypotheses hold on regular Gap3Lin through DKKMS by Corollary DK^C of
`value-free-star-list-references-put-np-in-rp`, with the budget `L` fixed
there. That corollary quantifies over all regular Gap3Lin inputs, so it covers the
planted and random inputs used below.

Theorem CLV gives one-sided success `>= theta c0^C_L / 2` per trial. This is
inverse-polynomial, because `theta >= 1/poly` and `c0^C_L` is a constant for
fixed parameters. So there is a randomized polynomial-time `A` that never
accepts a NO input and accepts every `x in P_0` with probability
`>= theta'(|x|) >= 1/poly(|x|)`. Hardcoding acceptance on `E_0`, as in
Corollary D, extends this to all of RU-YES.

## Step 3: the distinguisher

This is the one-sided case of Corollary PR of
`planted-regular-3lin-inputs-are-robustly-unique` (ESTABLISHED). By Theorem PR
there:
* a planted draw from `M(n, D, eps/2)` lies in RU-YES at every radius
  `rho in [0.061/k, (1 - beta0)/(12k))` and every `r0 >= 0`, except with
  probability `<= 3 e^(-0.2 n)`;
* a random draw lies in NO, except with probability `<= e^(-0.14 n)`.

Accept if any of `ceil(n/theta'(n))` independent runs of `A` accepts. This
accepts planted draws with probability `>= 1 - e^(-n) - 3e^(-0.2 n)` and
random draws with probability `<= e^(-0.14 n)`, so the advantage is
`1 - exp(-Omega(n))`. The input size is `poly(n)`, since `m = Dn/3` with `D`
a constant, so the running time is polynomial. This is the target.

## Where the gap is

Steps 2 and 3 are complete given their prerequisites. Among those,
`planted-regular-3lin-inputs-are-robustly-unique`,
`selector-witness-hypotheses-collapse-to-selector-free-form` and
`value-free-star-list-references-put-np-in-rp` are ESTABLISHED. The one open
prerequisite is (P2^RU).
