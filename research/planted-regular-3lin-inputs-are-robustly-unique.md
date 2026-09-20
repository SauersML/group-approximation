---
rg: 2
id: planted-regular-3lin-inputs-are-robustly-unique
kind: claim
title: Planted noisy 3LIN on D independent random triangle factors (D >= max(2*10^4 k^2, 20/eps^2)) is, with probability 1 - exp(-Omega(n)), a regular Gap3Lin(1 - eps, 1/2 + eps) YES input satisfying RU_(eps + gamma'/(4k), 0.061/k, 0) with C = 0, and the same model with uniform right-hand sides is a NO input -- so RU-YES is non-empty at every DKKMS parameter, and (RU-YES, NO) in BPP (or RP) would distinguish planted from random regular sparse 3LIN
distinct_from:
  hastad-images-are-never-robustly-unique: that shows the standard Håstad YES images are never robustly unique; this exhibits a different source (random planted regular 3LIN) that is robustly unique with C = 0, and that is average-case hard under the sparse-LPN / random-3XOR hypothesis.
  robust-uniqueness-bounds-robust-kernel-rank: that defines RU and gives the sufficient condition Proposition T (linear robust testability at every scale); this proves RU from a threshold expansion that is only needed for sets of density >= 0.06/k, which random regular hypergraphs satisfy, and never uses small-set expansion.
  gap3lin-hard-with-robustly-unique-yes-solutions: that is the worst-case NP-hardness statement (P1^RU), still open; this is an average-case membership statement about random inputs and implies no NP-hardness.
  locally-read-witnesses-are-sound-on-planted-2to1-inputs: that is about witnesses on planted 2-to-1 game inputs; this is about the 3LIN source and the RU promise, with no selector or witness.
artifacts:
  - experiments/ugc-planted-ru-2026-09-17/check_planted_ru.py
  - experiments/ugc-planted-ru-2026-09-17/check_planted_ru.out
---

**ESTABLISHED.** Route: `planted-regular-3lin-inputs-are-robustly-unique-proof`.

## Setting

This node is about the robust-uniqueness class RU-YES of
`gap3lin-hard-with-robustly-unique-yes-solutions` (P1^RU) and the notions of
`robust-uniqueness-bounds-robust-kernel-rank`. Here is the self-contained
version.

* A 3LIN instance has variables `X = [n]` and a list `Eq` of `m` equations
  `x_a + x_b + x_c = b_e` on three distinct variables. It is *regular* when
  every variable lies in the same number of equations.
* The DKKMS A-side tuples `U` are uniform ordered `k`-tuples of pairwise
  variable-disjoint equations. `omega(e) := (1/k) E_U[# slots of U equal e]`
  and `nu(T) := (1/(3k)) E_U[# variable slots of U in T]`.
  `val_omega(a)` is the `omega`-mass of equations `a` satisfies, and
  `dist_nu(a, b) := nu({v : a_v != b_v})`.
* **RU_(kappa, rho, r0)**: there are `x*` and a subspace `C` with
  `dim C <= r0` such that every `a` with `val_omega(a) >= 1 - kappa` has
  `dist_nu(a, x* + C) <= rho`.
* Constant-bias DKKMS constants: `k >= 3`, `0 < gamma' < gamma <= 0.105`,
  `k eps <= gamma/4` (this is implied by `2 k eps_3 <= gamma/2`), and the
  genericity threshold `beta0 < 0.11` of Corollary M.

**Model `M(n, D, eta)`.** `3 | n`. Draw `D` independent uniform permutations
`pi_1, ..., pi_D` of `[n]`. Factor `j` contributes the `n/3` equations on the
triples `{pi_j(3i-2), pi_j(3i-1), pi_j(3i)}`. So `m = Dn/3` and every variable
lies in exactly `D` equations.
* **Planted:** `x*` uniform in `F_2^n`, `b_e = x*(e) + xi_e` with
  independent `xi_e ~ Bernoulli(eta)`.
* **Random:** `b` uniform in `F_2^m`.

## Statement

**Theorem PR.** Let `k >= 3`, `gamma`, `gamma'`, `eps` be as above, with
`eps > 0`. Put

```text
D  >=  max(2 * 10^4 * k^2,  20 / eps^2),        n  >=  max(900 k^2,  36 k^2 / eps),
kappa := eps + gamma'/(4k),                     rho* := 0.061 / k .
```

1. **(YES)** With probability `>= 1 - 3 exp(-0.2 n)` over the planted model
   `M(n, D, eps/2)`, the instance is regular, `x*` satisfies a
   `1 - 3eps/4` fraction of `Eq`, `val_omega(x*) >= 1 - eps`, and
   (RU_(kappa, rho*, 0)) holds with `x*` and `C = {0}`.
2. **(NO)** With probability `>= 1 - exp(-0.14 n)` over the random model,
   every assignment satisfies at most a `1/2 + eps/2` fraction of `Eq`, and
   `val_omega(a) <= 1/2 + eps` for every `a`.

Since `rho* = 0.061/k < 0.0741/k < (1 - beta0)/(12k)` and `r0 = 0 <= l + 1`,
planted instances lie in RU-YES for every admissible radius
`rho in [rho*, (1 - beta0)/(12k))`, and random instances lie in NO, both with
probability `1 - exp(-Omega(n))`.

**Remark S (other soundness values).** The DKKMS nodes write the source
problem as `Gap3Lin(1 - eps_3, s*)` for a soundness constant `s* > 1/2`. Put
`sigma := min(eps, s* - 1/2)` and require `D >= max(2 * 10^4 k^2, 20/sigma^2)`
and `n >= max(900 k^2, 36 k^2/sigma)`. Then item 1 is unchanged, and item 2
becomes `val_unif(a) <= 1/2 + sigma/2 <= s*` and `val_omega(a) <= 1/2 + sigma`
for every `a` (route, Step 5 with `eps` replaced by `sigma` there). So random
instances are NO inputs for every such `s*`, in the uniform sense.

**Corollary PR (average-case content of (P1^RU)).** Let `A` be a randomized
polynomial-time algorithm and `rho in [rho*, (1 - beta0)/(12k))`.
* If `A` accepts every large RU-YES input with probability `>= 2/3` and every
  large NO input with probability `<= 1/3` (BPP), then running `A` `r` times
  and taking the majority distinguishes planted `M(n, D, eps/2)` from random
  `M(n, D, eps/2)` with advantage `>= 1 - 2 exp(-Omega(r)) - 4 exp(-0.14 n)`.
* If `A` accepts every large RU-YES input with probability `>= theta(n)`,
  `theta` inverse-polynomial, and never accepts a NO input (the RP form that
  Theorem CLV produces), then running it `n / theta(n)` times and accepting
  if any run accepts gives advantage `>= 1 - exp(-n) - 4 exp(-0.14 n)`.

In both cases, planted inputs lie in RU-YES and random inputs lie in NO
outside an event of probability `exp(-Omega(n))`, by Theorem PR. So:

> **(RU-YES, NO) in BPP, or a one-sided RP-type algorithm with inverse-polynomial
> success on RU-YES, refutes the sparse-LPN hypothesis for random regular
> 3-sparse equations at constant density `D` and constant noise `eps/2`.**

That hypothesis (planted 3XOR with `m = O(n)` equations and constant noise
is indistinguishable from random in polynomial time) is the standard one
behind Alekhnovich's cryptosystem and random 3XOR refutation below `n^(1.5)`
equations. It is a hypothesis, not a theorem; see the route's last section.

## Sanity checks

`experiments/ugc-planted-ru-2026-09-17/check_planted_ru.py` (output in
`check_planted_ru.out`) checks:
* **A.** The whole constant chain of Steps 3-6 in exact rationals at the
  worst admissible parameters (`k eps = gamma/4 = 0.02625`, `gamma' -> 0.105`,
  `beta0 = 0.11`), for `k = 3..200`.
* **B, C.** `q'(p) = 3(1 - 2p)^2`, so `q` is increasing, and
  `|q_n(w) - q(w/n)| <= 3/n` for the exact hypergeometric parity probability,
  `n <= 240` (the observed maximum of `n |q_n - q|` is `1.56`).
* **D.** The slot-measure bounds of Step 1, by enumerating all legitimate
  ordered `k`-tuples on five small regular instances.
* **E.** Brute force over all `2^n` assignments on three planted instances with
  `n in {18, 21}`. It prints the minimum odd-equation fraction at each weight
  and confirms `#odd(a + x*) <= viol(a) + viol(x*)`. In each case, every `a`
  with `viol(a) <= viol(x*) + 0.1 m` equals `x*`. This is only an
  illustration, since the theorem is asymptotic.

## What this changes (impact type 3: belief-changing)

* **P2^RU is not vacuous.** Falsifier 2 of
  `dkkms-orientations-admit-star-lists-on-robustly-unique-inputs` ("RU at
  scale `1/k` is incompatible with the DKKMS soundness regime, so RU-YES is
  empty") is refuted. RU-YES contains exponentially many inputs of every
  large size, at every DKKMS parameter, with `r0 = 0`.
* **The Håstad kill does not make RU easy.** Together with
  `hastad-images-are-never-robustly-unique`, the picture is: RU fails on the
  standard hardness images, but RU-YES versus NO is average-case hard under
  sparse LPN. Falsifier 1 of (P1^RU) ("(RU-YES, NO) in BPP") would break that
  hypothesis. Robust uniqueness does not make Gap3Lin easy unless planted
  sparse 3XOR is easy.
* **A second, average-case form of the constant-bias kill.** Corollary D's
  proof gives `(P_0, NO) in RP` without using hardness. So `sel` together with
  (P2^RU) already breaks planted regular sparse 3LIN, with no appeal to
  (P1^RU). This is the OPEN node
  `constant-bias-dkkms-selectors-break-planted-sparse-3lin`, whose only
  non-established prerequisite is (P2^RU).
