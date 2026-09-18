---
rg: 2
id: degree-one-laplacian-gap-forces-kesten-gap-in-every-model
kind: claim
title: A degree-one Laplacian gap forces the degree-zero Kesten gap in the same model, so maximal higher Kazhdan projections in degree one are Kazhdan and add no rung to the spectral-gap ladder
distinct_from:
  model-spectral-gap-quantifier-ladder: that proves the degree-zero isolated-eigenvalue substitute (MSG) is a Kazhdan theorem when quantified over all representations, and records the undecided tracial and stably finite rungs; this shows the degree-one Laplacian of any presentation complex is never a weaker substitute, at any rung, because its gap implies (MSG) in the same model with the same constant.
  reduced-higher-kazhdan-projection-kk-witness: that records Li--Nowak--Pooya higher Kazhdan projections in the reduced algebra and what a non-integer trace would refute; this shows their maximal-algebra degree-one analogue exists only for Kazhdan groups, so the reduced projections cannot be transported into corona models as a Property-(T)-free source of corners.
  kesten-spectral-gap-replaces-kazhdan-projection-per-model: that isolates (MSG) as the only Kazhdan input of the transport; this closes the cohomological escape from it in degree one.
---

**ESTABLISHED (written proof; not Lean-verified).**  This is an obstruction
to a class of approaches.

**Setting.**  `L` is a group with finite generating set `S_0` and relator set
`R`.  Let `d_0 in M_(S_0 x 1)(Z[L])` be the column `(s-1)_s`, and let
`d_1 in M_(R x S_0)(Z[L])` be the matrix of images of the Fox derivatives
`d r/d s`.  Put

```text
Delta_0 = d_0^* d_0 = sum_(s in S_0) (2 - s - s^(-1)),
Delta_1 = d_0 d_0^* + d_1^* d_1  in M_(S_0)(Z[L]),
```

the degree-zero and degree-one Laplacians of the presentation complex.  For
a unital C-star algebra `A` and a homomorphism `rho: L -> U(A)`, write
`rho` also for the induced map on matrices.

**Theorem.**
1. **Per-model transfer.**  If `sp(rho(Delta_1))` misses `(0,eps)`, then
   `sp(rho(Delta_0))` misses `(0,eps)`.  Hence `(MSG)` holds on `L` for
   `rho` in the notation of `model-spectral-gap-quantifier-ladder`, for the
   generating set `S = {e} u S_0 u S_0^(-1)`, with a constant depending only
   on `eps` and `|S_0|`.  No hypothesis on `A`, on `rho`,
   or on `R` is used beyond `d_1 d_0 = 0`.
2. **Maximal degree-one projections are Kazhdan.**  If `0` is isolated in
   the spectrum of `Delta_1` in `M_(S_0)(C*_max L)`, so that the maximal
   higher Kazhdan projection `p_1 = chi_{0}(Delta_1)` exists, then `L` has
   property `(T)` with Kazhdan pair `(S_0, sqrt(eps/|S_0|))`.
3. **No new rung.**  For every class of targets (all Hilbert spaces, corona
   algebras, finite von Neumann algebras, stably finite C-star algebras), a
   degree-one Laplacian gap along every model of the class implies `(MSG)`
   along every model of that class, with the same constant.  So a
   degree-one hypothesis is never a strictly weaker prerequisite than the
   degree-zero one on any rung of the ladder.
4. **Calibration.**  For `L = F_m`, `m >= 2`, with `R` empty, `Delta_1 = d_0 d_0^*`.
   In `C*_r F_m` it is gapped (Kesten), and `p_1` exists as Li--Nowak--Pooya
   record.  In `C*_max F_m` it is not gapped, since `F_m` does not have
   `(T)`.  So the gap between reduced and maximal higher projections is
   exactly the Kazhdan gap in degree zero.

**The class it kills.**  These are arguments that remove property `(T)` from
the manuscript transport by producing an ambient-invariant corner from a
gapped higher Laplacian instead of the Kazhdan projection.  Examples are
Li--Nowak--Pooya projections, Euler characteristic identities
`sum (-1)^k [p_k]` in `K_0` of a corona model, or `l2`-Betti bookkeeping.
Every member dies at one step: restricting `Delta_1` to the closure of
`range d_0`.  The invariant is the orthogonal splitting
`Delta_1 = d_0 d_0^* + d_1^* d_1` with `(d_0 d_0^*)(d_1^* d_1) = 0`, together
with `sp(TT^*) u {0} = sp(T^*T) u {0}`.  Degree one is special because
`Delta_0` has only the summand `d_0^* d_0`, so the lower half of `Delta_1`
is all of `Delta_0`.  In degree `n >= 2` the same splitting only controls the
upper half `d_(n-1)^* d_(n-1)` of `Delta_(n-1)`, and the induction stops.

**What survives.**  Degree-zero data (invariant vectors of `L`, the only
place a defect corner can live) enters any cochain Euler relation only
through `p_0` or `p_1`.  Truncated complexes `0 -> C^1 -> C^2 -> ...` have
gapped Laplacians without `(T)`, but their lowest projection is
`[ker d_1] = [p_1] + [closure range d_0]`, and it does not split off a
degree-zero corner.  Whether gapped Laplacians in degrees `n >= 2` carry any
MF-radical information is not decided here.

Proof route: `degree-one-laplacian-gap-forces-kesten-gap-in-every-model-proof`.
