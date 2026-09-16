---
rg: 2
id: klingen-central-quotient-min-inexact-proof
kind: route
title: Lift the twisted ISW gap element to the Klingen extension and kill the centre ideal with nearby genuine twisted blocks
target: klingen-central-quotient-is-min-inexact
requires: []
artifacts:
  - research/artifacts/klingen-central-quotient-2026-09-16.md
---

The full proof is in `research/artifacts/klingen-central-quotient-2026-09-16.md`:

- §0: matrix model (F1)–(F5);
- §1: fibre maps (1.1);
- §2: Lemma B;
- §3: Theorem 1, Steps 1–7, at `t = 0`;
- §3A: Theorem 1', at every `t`.

All ISW input is cited by source line (arXiv:2006.01874).

1. **Model.**
   - `N(v,c) = I + X_v + cZ` and `L(g)` satisfy
     `N(v,c) N(w,d) = N(v+w, c+d+omega(v,w))` and
     `L(g) N(v,c) L(g)^{-1} = N(gv, c)`.
   - So `E = {N(v,c) L(g)}` is `Z x_c Lambda`, with ISW's cocycle
     `c = omega(v, g w)`.
   - Hand proof: `X_v X_w = omega(v,w) Z`, and all other products vanish.  This
     is also machine-checked in
     `experiments/sp2g-z-full-c-star-algebra-has-llp-2026-09-16/klingen_structure.py`.

2. **Blocks.**
   - Pick rationals `s_n = p_n/k_n -> t` with `0 < |s_n - t| < 1/2`.
   - Reduce `E` mod `k_n`.  In `l^2(E_{k_n})`, the `e^{2 pi i s_n}`-eigenspace of
     the central element gives a genuine `rho_n` with `rho_n(z) = e^{2 pi i s_n}`.
   - `pi_n = rho_n(0, .)` is `sigma_{s_n}`-projective.

3. **Upper bound.**
   - ISW Claim `gap` (lines 697–704) gives `g_1, ..., g_m` and `D < m`.  It
     bounds `||sum pi(g_i)||` by `D` for every projective `pi` whose cocycle is
     not a coboundary on `Z^2`.  This rests on NPS for arbitrary projective
     representations, ISW line 552.
   - `W_u (x) conj(pi_n)` has cocycle `sigma_{t - s_n}`.  On `(e2, f2)` its
     antisymmetrization is `e^{4 pi i (t - s_n)}`, which is not `1`.
   - Hence `||(q_t (x) id) t~||_{A_t (x)_min B} <= D`, where `B = prod M_{d_n}`.

4. **Lower bound.**
   - `Theta = corona o (rho_n (x) ev_n)_n` is a *-homomorphism.
   - It kills `I_t (x)_min B`, because
     `||rho_n((u_z - e^{2 pi i t}) x)|| <= |e^{2 pi i s_n} - e^{2 pi i t}| ||x|| -> 0`.
   - It gives `||Theta(t~)|| = m`, via the maximally entangled vector.
   - So `dist(t~, I_t (x)_min B) >= m > D`.  The induced quotient map is not
     isometric, so it is not injective.

5. **No local lift.**  A ucp lift `s` of `span{1, W_t(g_i), W_t(g_i)^*}` would
   put `t~ - (s (x) id) t_t` in `I_t (.) B`.  Then
   `dist(t~, I_t (x)_min B) <= D`, which contradicts step 4 (Lemma B).

6. **To `B(l^2)`.**  Use the block-diagonal conditional expectation
   `P : B(l^2) -> B`.  The map `id (x) P` is contractive, fixes `t~`, and maps
   `I_t (x)_min B(l^2)` into `I_t (x)_min B`.
