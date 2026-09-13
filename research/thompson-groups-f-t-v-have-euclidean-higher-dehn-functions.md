---
rg: 2
id: thompson-groups-f-t-v-have-euclidean-higher-dehn-functions
kind: claim
title: "For every k >= 2 the k-dimensional Dehn functions of Thompson's groups F, T and V are euclidean, n^((k+1)/k)"
distinct_from:
  thompson-f-has-quadratic-dehn-function: that is the classical (k = 1) Dehn function of F, established by Guba; this is the conjecture for all higher dimensions k >= 2 and for F, T and V together.
---

**Open.** Conjecture (the higher-rank part of Zaremsky Problem 2.5, "are they
all euclidean?"): for every `k ≥ 2` and every `G ∈ {F, T, V}`, the homotopical
k-dimensional Dehn function satisfies `δ^(k)_G(n) ≃ n^((k+1)/k)`.

The groups are of type `F_∞`, so `δ^(k)_G` is defined for every `k`
(Alonso–Wang–Pride 1999) and is a quasi-isometry invariant up to `≃`. The
homological version is a separate question (Abrams–Brady–Dani–Young, PNAS
2013, show the two can differ). A negative answer is an explicit different
computation of some `δ^(k)_G`.

## Attempts

- **Literature.** A bounded search on 2026-09-13 (web and arXiv, "higher
  dimensional Dehn function" together with "Thompson") found no computation of
  `δ^(k)` for `k ≥ 2` for F, T or V. The `k = 1` cases: F quadratic (Guba 2006),
  T quadratic (Migliorini 2025), V open
  (`thompson-v-has-quadratic-dehn-function`).
- **Lower-bound idea.** F contains `Z^m` for every `m` (elements with disjoint
  supports). An undistorted `Z^(k+1)` does not by itself force
  `δ^(k) ≽ n^((k+1)/k)`. One also needs a coarsely Lipschitz retraction onto the
  flat, or a volume-distortion argument in the style of
  Brady–Bridson–Forester–Shankar. Test whether F admits coarse retractions onto
  its disjoint-support flats; F's linear isodiametric function (Guba 2006,
  Corollary 1) and the product structure of disjoint supports are the natural
  tools.
- **Upper-bound idea.** Brown's proof that F, T and V are of type `F_∞` uses a
  Morse function on the Stein–Farley complex, a CAT(0) cube complex that is
  infinite-dimensional and locally infinite, whose descending links are highly
  connected at large heights. Fill k-spheres inside a cocompact sublevel set by
  pushing down along descending links, and count volume per height. The risk
  is that the connectivity of descending links grows only linearly in height,
  so fillings may need to climb.
- Nothing here is attacked in depth yet; lane z2-05-v-dehn works the V part
  first.
