---
rg: 2
id: near-exact-tuples-saturate-linear-conversion-defect
kind: claim
title: Rank-one perturbations of finite permutation representations of SL_n(Z) have conversion defect exactly L and commutator growth exactly 2L, so relators never force a sublinear conversion defect
distinct_from:
  sln-relators-force-linear-commutator-growth: that proves the upper bounds phi(L) <= C_n k L and conversion defect <= C_n k L for n >= 5; this proves both are sharp, with tuples at rank distance one from an exact representation, for every n >= 2 and every presentation, and refutes the sublinear upgrade asked for there.
  hs-length-control-is-linear-under-stability: that is the normalized HS telescoping bound for trivial words under stability; this is the unnormalized rank version together with a matching lower bound, used to locate the noise floor of every word-growth invariant.
  deligne-cover-bounded-rank-sector-tuples-have-bounded-dimension: that is the bounded-rank rung itself; this kills one proposed sub-step of its long-root route (sublinear conversion defect) and replaces it by the rectangle-profile question.
artifacts:
  - research/near-exact-tuples-saturate-linear-conversion-defect-proof.md
  - experiments/near-exact-noise-floor-2026-09-17/noise_floor.py
  - experiments/near-exact-noise-floor-2026-09-17/noise_floor.out
---

**ESTABLISHED (unreviewed)** (`near-exact-tuples-saturate-linear-conversion-defect-proof`). Elementary.
It refutes step (a) of the wave-5 brief on the long-root route.

**Setting.** `Gamma = SL_n(Z)`, `n >= 2`, with any finite presentation `<S | R>` whose generators
include the elementary matrix `u = e_12`. A rank-`k` tuple is `rho : S -> U(d)` with
`rank(rho(r) - I) <= k` for all `r` in `R`. The **conversion defect** of a word `W` with `W = u^L`
in `Gamma` is `rank(rho(u)^L - rho(W))`. For a commuting root pair `u, v` put
`phi(L) = rank(rho([u^L, v^L]) - I)`.

**Theorem.** Fix a prime `p` and a unit `lambda != 1`. Let `pi` be the permutation representation of
`SL_n(Z)` on `C[F_p^n]`, so `d = p^n`. Define `rho = pi` on `S \ {u}` and `rho(u) = pi(u) D`, where
`D` multiplies the one basis vector `delta_(x_0)` by `lambda`, with `x_0 = e_2 + e_3` (for
`n = 2`, `x_0 = e_2`; there only parts 1 and 2 apply). Then:

1. **Rank-`k` tuple at rank distance one.** `rank(rho(r) - I) <= |r|_u` for every relator `r`, where
   `|r|_u` counts the letters `u^(+-1)` in `r`. So `rho` is a rank-`k` tuple with
   `k = max_r |r|_u`, and `rank(rho(s) - pi(s)) <= 1` for every generator `s`.
2. **Conversion defect is exactly linear.** For `1 <= L <= p` and every word `W` with `W = u^L` in
   `Gamma`,

   ```text
   L - |W|_u  <=  rank(rho(u)^L - rho(W))  <=  L + |W|_u.
   ```

   The lower bound is `L - O(log^2 L)` for the LMR shortcut words `W_L`. For `n >= 3` it is exactly
   `L` for the Steinberg word `W = [e_13^a, e_32^b]`, `ab = L`, which has length `2(a + b)` and
   no letter `u`.
3. **Commutator growth is exactly linear.** For `v = e_13` and `2L <= p`, `phi(L) = 2L`.

**Consequences.**

- **Question (a) is false.** The relators of `SL_5(Z)`, or of any `SL_n(Z)`, do not force
  `rank(rho(u)^L - rho(W_L(u))) = o(L)`. The upper bounds `C_n k L` of
  `sln-relators-force-linear-commutator-growth` are sharp in `L`, and the sharpness is witnessed by
  tuples at rank distance one from an exact representation. So a sublinear conversion defect cannot be
  the input to joint-spectrum rigidity. The same tuples also kill atom-level rigidity of the spectrum of
  `rho(u)` itself: on the `p`-cycle of `pi(u)` through `x_0` every eigenvalue is rotated by a
  `p`-th root of `lambda`, so `p` atoms move (and `p` is arbitrary), yet the tuple rounds to `pi` at
  rank one.
- **The noise floor (Lemma A in the proof).** If `rank(rho(s) - pi(s)) <= r` for all `s` in `S`, with `pi` exact, then
  `rank(rho(w) - I) <= r |w|` for every word `w` trivial in `Gamma`. With the theorem, every
  word-growth invariant of trivial words of length `O(L)` has its near-exact noise floor at order `L`.
  Such invariants can only detect distance from exact representations through **superlinear**
  growth.
- **Distance lower bound (Lemma B).** For unitaries `b, c` and any commuting `b', c'` on `C^d (+) C^m`,
  `max(rank(b' - b (+) beta), rank(c' - c (+) gamma)) >= Lambda(b,c)`, where
  `Lambda(b,c) = sup_w rank(w(b,c) - I) / |w|` and `w` ranges over the words trivial in `Z^2`.
  In particular the distance is at least `sup_L phi(L) / (4L)`.
- **Correction to the wave-5 premise.** The slit origami is not an example of a pair with linear
  `phi` that is far from commuting. Its profile is quadratic up to the slit scale:
  `phi(m) = 2 m^2` for `m <= floor(L/2)` (computed for `L = 4..14` in `noise_floor.out`). The
  dislocation dipole of `z2-commuting-pairs-are-not-bounded-rank-stable` is quadratic by its own
  area-law computation. So by `sln-relators-force-linear-commutator-growth`, neither family can occur as a
  direct summand of the long-root pair of a rank-`k` tuple of `SL_5(Z)` (or of a Deligne sector tuple
  with `g >= 5`) beyond scale `O(k)`: `2 m^2 <= C_5 k m` forces `m <= C_5 k / 2`.
- **What survives.** On this route the only question left for `g >= 5` is B-invariant. Does a
  **bounded linear rectangle profile**,
  `rank([B^a, C^b] - I) <= K (a + b)` for all `a, b >= 1`, force rank distance `<= F(K)` from
  commuting pairs? This is `z2-bounded-rectangle-profile-forces-near-commuting`. By Lemma B the
  converse holds with `K = 2 dist`. No Z^2 pair is known that has a bounded linear profile and is far
  from commuting.

**Calibration.** Exact representations give defect 0. The Wollmilchsau tuples of
`sl2-relators-do-not-force-linear-commutator-growth` have `phi = 12 L^2`, above the floor. The
theorem needs only a finite quotient in which `u` has order `>= L`, so it applies to every residually
finite group and every generator of infinite order. It does not apply to Deligne sector tuples
themselves, which have no exact finite-dimensional model. What it kills there is every argument that
uses only the relators of a residually finite subgroup, such as the `SL_g(Z)` Levi, to prove a
sub-noise-floor bound.
