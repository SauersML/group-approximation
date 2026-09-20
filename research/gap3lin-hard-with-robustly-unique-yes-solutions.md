---
rg: 2
id: gap3lin-hard-with-robustly-unique-yes-solutions
kind: claim
title: (P1^RU) Regular Gap3Lin(1 - eps, 1/2 + eps) stays NP-hard under Karp reductions when YES instances are promised robust uniqueness at scale 1/k -- every assignment of omega-value >= 1 - eps - gamma'/(4k) is within nu-distance rho < (1 - beta0)/(12k) of one coset x* + C with dim C <= r0 <= l + 1
distinct_from:
  exact-kernel-rank-does-not-exclude-flip-violators: that states (P1^rob), hardness on the class P^delta_r defined by excluded approximate kernel maps; this is a stronger, source-side hardness statement that implies (P1^rob) by Corollary M of robust-uniqueness-bounds-robust-kernel-rank.
  good-dkkms-orientations-admit-short-star-lists-on-hard-inputs: that is (SF_P) with the exact-kernel hardness (P1), now refuted as a whole; this is only a hardness prerequisite and says nothing about star lists.
  robust-uniqueness-bounds-robust-kernel-rank: that proves robust uniqueness excludes generic approximate kernels of rank above r0; this asks whether robustly unique YES instances stay NP-hard.
  parity-leaking-branch-selectors-reach-near-perfect-completeness: that is the selector hole H1; this is one of the two prerequisites of the robust-uniqueness route to the constant-bias kill and does not mention selectors.
---

**OPEN.**

## Statement

Fix the DKKMS parameters `(k, l, beta)` with `l >= 8`, the constant-bias
constants `0 < gamma' < gamma <= 0.105`, and the genericity threshold `beta0`
of `robust-uniqueness-bounds-robust-kernel-rank` (Corollary M). Use the
measures `omega` and `nu` of that node: the equation and variable-slot
marginals of the DKKMS tuple distribution.

**Claim (P1^RU).** For some `r0 <= l + 1` and some `rho < (1 - beta0)/(12k)`,
the promise problem `(RU-YES, NO)` is NP-hard under Karp reductions. Here
RU-YES is the set of regular Gap3Lin inputs of completeness `1 - eps` that
satisfy (RU_(eps + gamma'/(4k), rho, r0)), and NO is the usual soundness side.

**Consequence.** By Corollary M this implies (P1^rob) with `r = r0`. Together
with `dkkms-orientations-admit-star-lists-on-robustly-unique-inputs`
(P2^RU), and by Corollary D of
`selector-witness-hypotheses-collapse-to-selector-free-form`, it gives the
constant-bias kill of H1 on DKKMS under NP not in RP (route
`constant-bias-dkkms-selectors-put-np-in-rp-via-robust-uniqueness`).

## Why it is open, and what would decide it

* **Sufficient condition (Proposition T).** It suffices that hard YES instances
  have a homogeneous system that is `eps0`-robustly testable, with
  `eps0 > (3 gamma' + 24 k eps)/(1 - beta0)` (about `0.36` at `gamma' = 0.105`,
  `k eps -> 0`), and with exact kernel of dimension `<= l + 1`. The upper limit
  is `eps0 <= 3`, so this is a constant-ratio condition. It must hold at every
  distance scale, including distance near `1/2`.
* **Håstad-format images (heuristic, not proved).** In the long-code image of
  a Label Cover instance, the assignments of near-optimal value include the
  encodings of every near-consistent labelling. Two different labellings give
  long-code tables at distance about `1/2`. So RU with small `r0` asks, roughly,
  for Label Cover YES instances whose near-optimal labellings are few up to a
  small linear span. The robust kernel rank then behaves like `log2` of the
  number of pairwise-far near-consistent labellings, whose differences are
  size-2 characters. We know of no hardness result of this robustly unique
  kind. Valiant–Vazirani isolation gives exact uniqueness of the optimum under
  randomized reductions. It says nothing about near-optimal solutions.
* **Gadget padding does not supply robust uniqueness at constant source share.** Let a reduction append
  gadget equations on fresh variables `Z` such that every assignment to the
  source variables `X` extends to one satisfying all gadget equations. Then the
  homogeneous gadget solutions project onto `F_2^X`. Choose a linear section
  `s`, and extend `Phi` to `Phi'` by requiring `<z, Phi'(e_v)> = s(y_z)(v)` for
  `v in Z`. This is linear in `z`. Every `y'_z = (y_z, s(y_z))` satisfies all
  homogeneous gadget equations, so `Phi'` kills every gadget equation and its
  dirty set is that of `Phi`. The rank is still `n`. The measures do change.
  Suppose the padded law puts mass `t` on source equations, with `t` times the
  old law there. Then the dirty mass scales by `t`, and the pairwise
  `nu`-distances of the family `x + y'_z` drop by at most the factor `t`,
  since `nu_new(v) >= (1/3) sum over source e containing v of omega_new(e)`
  equals `t nu_old(v)`. By Proposition C on the source, the padded instance keeps `2^n`
  near-solutions at pairwise distance `D >= t (1 - beta_old)/(3k)`. Two of
  them must share a nearest coset point when `r0 < n`, so RU forces
  `D <= 2 rho`. So RU fails at every admissible `rho < (1 - beta0)/(12k)`
  whenever `t (1 - beta_old) >= (1 - beta0)/2`. The gap needs `t` to be a
  constant, so this kind of padding produces RU only by a dilution that costs
  a constant factor of the gap. Robust uniqueness has to come from the source
  hardness (the PCP) itself.
* **Deterministic reductions.** A Karp reduction onto a promise of "few
  near-optimal solutions" is at least as demanding as deterministic
  few-solution hardness, which is not known even for exact uniqueness. A
  version of Corollary D for randomized one-sided reductions would remove this
  issue. The CLV decoder is certificate-based, so such a version looks
  routine, but it has not been checked.

## Falsifiers

* A proof that `(RU-YES, NO)` is in BPP (a falsifier under NP not in BPP) or
  in coNP (under NP != coNP), or more generally that
  robust uniqueness at scale `1/k` makes Gap3Lin easy.
* A structural theorem saying that NP-hard Gap3Lin YES instances with
  completeness `1 - eps` always carry robust near-kernels of rank above `l + 1`.
  One route would be to show that every reduction from 3SAT leaves the
  2^(Omega(n)) witness freedom as a near-linear family.

## Attempts

* **2026-09-20, swarm-0917-w20-w20-ugc-pull (finite-models / transplanter).**
  Isolated this statement as the source-side form of (P1^rob), via
  Corollary M of `robust-uniqueness-bounds-robust-kernel-rank`. Recorded the
  gadget obstruction and the testability sufficient condition. No hardness
  was attempted.
* **2026-09-20, swarm-0917-w21-w21-ugc-follow (probability-random).**
  Settled the average-case side, but not the NP-hardness. See
  `planted-regular-3lin-inputs-are-robustly-unique` (ESTABLISHED). Planted noisy
  3LIN on `D >= max(2*10^4 k^2, 20/eps^2)` random triangle factors is, with
  probability `1 - exp(-Omega(n))`, a regular YES input satisfying
  (RU_(eps + gamma'/(4k), 0.061/k, 0)) with `C = 0`. The same model with
  uniform right-hand sides is a NO input. The proof uses a threshold expansion
  (every set of density `>= 0.06/k` has odd-equation fraction `>= 0.09/k`, by
  Azuma over the permutations), and the fact that `a + x*` is odd only on
  equations violated by `a` or by `x*`. Consequences for this node:
  * Falsifier 1 (`(RU-YES, NO) in BPP`) would refute sparse LPN for regular
    random 3XOR at constant density (Corollary PR). So robust uniqueness at
    scale `1/k` does not make Gap3Lin easy unless planted sparse 3XOR is easy.
  * RU-YES is non-empty at every DKKMS parameter, with `r0 = 0`.
  * For the downstream kill, this node can be bypassed.
    `constant-bias-dkkms-selectors-break-planted-sparse-3lin` (OPEN, only
    (P2^RU) missing) gets `sel => planted sparse 3LIN is distinguishable`
    with no hardness prerequisite, because Corollary D's proof shows
    `(P_0, NO) in RP` before the Karp step.
  The worst-case NP-hardness asked here is untouched. Random planted
  instances are not produced by a Karp reduction, and the Håstad images are
  not robustly unique (`hastad-images-are-never-robustly-unique`). A
  reduction whose YES images are random-like expanders is still needed.
