---
rg: 2
id: commuting-translations-sharing-an-inflow-ray-are-not-realizable
kind: claim
title: Two commuting near permutations that drain the same ray into different rays admit no genuine realization, so any near action containing such a pair is not realizable
distinct_from:
  one-ended-near-regular-actions-have-a-realization-defect: that is an integer defect for near-regular actions of one-ended groups; this is a local obstruction for any near action, carried by one commuting pair of ray translations.
  lamplighters-in-v-show-near-action-neatness-is-no-bh-obstruction: that concerns neatness and profinite finite presentation of inputs; this is an elementary non-realizability criterion used on host groups.
artifacts:
  - research/artifacts/gq-bh-bh-shell-arith-lsf-mixed-radix.md
---

**ESTABLISHED** (lane proof, elementary, not reviewed; no novelty claimed). Cornulier (arXiv:1901.05065,
§`i_kapou`) attaches a Kapoudjian class to near actions and records that Houghton near actions of `Z^d`
have nonzero class. The statement below is an elementary instance of this phenomenon, proved directly
for realizations on any set commensurate with `N`.

## Statement

Let `a, b` be near permutations of a countable set `N` that commute in `NearSym(N)`. Suppose there are
pairwise disjoint injective sequences (rays) `p_t, q_t, r_t` (`t >= 0`) in `N` and integers `m, n >= 1`
such that, for all but finitely many points of `N`:
- `a` sends `p_t -> p_(t-m)` and `q_t -> q_(t+m)`, and fixes every other point (in particular every `r_t`);
- `b` sends `p_t -> p_(t-n)` and `r_t -> r_(t+n)`, and fixes every other point (in particular every `q_t`).

Then `<a, b>` has no realization: there is no set `Y` with `Y △ N` finite carrying commuting genuine
permutations `alpha, beta` that agree with `a, b` outside a finite set. Hence no near action containing
such a pair is realizable.

## Proof

Let `alpha, beta` be such a realization, with a finite set `F` outside which both agree with the models.
- *The bi-infinite `alpha`-orbits.* Orbits of a permutation are cycles or bi-infinite. Outside `F`,
  `alpha` moves points only down the `p`-ray (toward `F`) and up the `q`-ray (away), and fixes all others.
  A bi-infinite orbit leaves every finite set in both directions. So its backward end lies in the
  `p`-ray and its forward end in the `q`-ray. Each residue class of the `p`-tail mod `m` lies in one
  orbit, so there are at most `m` bi-infinite orbits. There is at least one, since the `p`-tail is
  infinite. Call them `O_1, ..., O_k`.
- *Commuting.* `beta` permutes the `alpha`-orbits and preserves the set of bi-infinite ones. So
  `gamma = beta^(k!)` preserves each `O_i`. On `O_i ≅ Z`, `alpha` is the unit translation, and a bijection
  of `Z` commuting with it is a translation. So `gamma|O_i = alpha^(e_i)|O_i` for some `e_i in Z`.
- *Contradiction.* Far out on the `q`-ray, `gamma` fixes points (since `beta` does), while `alpha^e` moves
  them by `e m`. So `e_i = 0`. Far out on the `p`-ray, `gamma` moves `p_t` to `p_(t - n k!)`, which is
  `alpha^(n k!/m)` there, a nonzero power. So `e_i != 0`. ∎

## Typical source

Localized translations along three pairwise disjoint arithmetic progressions: `a = a_(d_0) a_(c')^-1`,
`b = a_(d_1) a_(c')^-1` in any group of piecewise translations of a completion `Z^`. These are, for example,
localized odometers on disjoint cones in odometer or Roever--Nekrashevych-type full groups, restricted to
the ray of nonnegative integer points. Any finite-index subgroup contains powers of both, which still
satisfy the hypotheses.
