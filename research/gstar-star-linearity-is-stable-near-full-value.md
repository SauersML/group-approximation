---
rg: 2
id: gstar-star-linearity-is-stable-near-full-value
kind: claim
title: (GStar_n) holds, uniformly in n and l, once the Grassmann star value is at least 0.923 (all-functionals list) or 0.9925 plus 2^(3-m) (a single global functional) -- the star mass is at most 5.5(1-val), by an exact Fano-plane charging constant 4/3 for twisted stars and BLR on the star quotient, and the per-star references glue across the Grassmann graph, whose second eigenvalue is below 1/2
distinct_from:
  list-star-coherent-selector-witnesses-put-np-in-rp: that node states (GStar_n) and leaves it OPEN at every value; this proves it in the high-value range val >= 0.923 (and with list size 1 at val >= 0.9925 + 2^(3-m)), for every n and every l >= 2, while the band 1/2 + gamma < val < 0.923 stays open.
  few-patch-witnesses-above-half-decode-outer-labels: that node's Lemma A shows that at value about 1/2 the star map can be an arbitrary function; this shows that near full value it is forced to be close to linear, with an explicit linear constant.
artifacts:
  - experiments/ugc-gstar-stability-2026-09-17/fano_twist.py
  - experiments/ugc-gstar-stability-2026-09-17/check_stability.py
---

**ESTABLISHED** (Theorems S and G). Route:
`gstar-star-linearity-is-stable-near-full-value-proof`.
This neither proves nor refutes UGC.

## Setting

Take the notation of (GStar_n) in
`list-star-coherent-selector-witnesses-put-np-in-rp`. `F` gives a linear
functional `F(S)` on every subspace `S <= F_2^n` of dimension `l-1` or `l`,
with `l >= 2`. Put `m := n-l+1`.

* `val := Pr_{W,u}[u notin W, F(W+u)|_W = F(W)]`, where `W` is a uniform
  `(l-1)`-space and `u` is uniform in `F_2^n`.
* An edge `(W,T)` with `W < T`, `dim T = l`, is *unsat* if
  `F(T)|_W != F(W)`. `eps_W` is the unsat fraction of the edges at `W`, and
  `eps := E_W eps_W`.
* For a functional `psi` on `F_2^n`, put
  `D_W(psi) := Pr_u[u notin W, F(W+u)|_W = F(W), F(W+u)(u) != psi(u)]`.

Then `1 - val = 2^-m + (1 - 2^-m) eps`, so `eps <= 1 - val`.

## Theorem S (star mass is linearly stable)

For every `n`, every `l >= 2` and every `F`:

    Dmin := E_W min_psi D_W(psi) <= 5.5 eps <= 5.5 (1 - val).

The minimum may be restricted to extensions `psi` of `F(W)`.

Consequently (GStar_n), with `Psi` the list of all `2^n` functionals, holds
whenever `val >= (6 + gamma')/6.5`, which is about `0.923 + gamma'/6.5`.

## Theorem G (one global reference)

For every `n`, every `l >= 2` and every `F`, some single functional `psi` has

    E_W D_W(psi) <= 65.5 eps + 2^(3-m).

So (GStar_n) holds with `|Psi| = 1` whenever
`val >= (66 + gamma' + 2^(3-m))/66.5`, which is about `0.9925`.

## Why it matters

* Through Theorem CL of `list-star-coherent-selector-witnesses-put-np-in-rp`,
  Theorem G gives (Star-List) with `L = 1`.
* It applies to every image-determined labelling of a J-instance, up to the
  transfer error `2^(l-k) + delta_sur` recorded there, whose Grassmann star
  value is at least `0.9925 + 2^(3-m)`.
* So, under `NP not in RP`, image-determined selector witnesses in the
  constant-bias cell of H1 must have star value below about `0.9925`. The
  all-functionals version lowers this to `0.923` when `2^n <= L_max`.
* The mechanism is new. A twisted star, meaning three satisfied edges whose
  labels have no common extension, is always paid for by nearby unsat edges,
  at an exact rate. The constant is 4/3 per Fano configuration (Lemma F7,
  exhaustive). It is attained, so the Fano route cannot give better than
  `t <= 4 eps`.

## What is left

* (GStar_n) in the band `1/2 + gamma < val < 0.923`. Near `val ~ 1/2` the
  statement is false for list size 1, by Lemma A of
  `few-patch-witnesses-above-half-decode-outer-labels`. The recorded
  counterexamples all have `val - 1/2 = O(2^-l)`.
* The whole problem is a threshold question. Is there a constant `c < 1`,
  independent of `l`, such that `val >= 1/2 + c/2` forces a short list? This
  node gives `c = 0.846`. A proof for all `c > 2^(2-l)` would close the
  image-determined case.
* General (non-image-determined) (Star-List) is untouched.

## Checks

* `experiments/ugc-gstar-stability-2026-09-17/fano_twist.py all` enumerates
  all `877 * 4^7` coloured Fano labellings. It finds max twisted/unsat `= 4/3`,
  attained at `(4, 3)` in the monochrome case, and checks that no fully
  satisfied Fano configuration has a twist. It runs in about four minutes.
* `experiments/ugc-gstar-stability-2026-09-17/check_stability.py 2` covers
  `(n,l) = (4,2), (5,2), (5,3), (4,3)`, on perturbed honest labellings and
  two-functional mixtures. It checks:
  * the per-`R` bound `3 tw_R <= 4 unsat_R`;
  * `Dmin_W <= t_W + 1.5 eps_W` at every `W`;
  * `t <= 4 eps`, `eps <= 1 - val` and `Dmin <= 5.5 (1 - val)`;
  * that the closed-form Grassmann ratio `theta_1/theta_0` matches the numeric
    second eigenvalue.

  It exits 0.

## Attempts

* 2026-09-19 (swarm-0917-w14-w14-ugc-follow): proved Theorems S and G. The
  approach is Fano sub-configuration charging plus BLR on the star quotient,
  then spectral gluing on the Grassmann graph `J_2(n, l-1)`. Tried and not
  pursued: pushing the charging below 4/3. That is impossible, because 4/3 is
  attained, so the 0.923 threshold is the limit of this route. The band below
  0.923 needs a genuinely different, non-local argument.
