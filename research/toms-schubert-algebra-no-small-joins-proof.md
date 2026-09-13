---
rg: 2
id: toms-schubert-algebra-no-small-joins-proof
kind: route
title: Thom--Porteous degeneracy plus branch traces bound every common Cuntz upper bound from below
target: toms-schubert-algebra-has-no-small-joins
requires: []
---

**Imports (read in the e-print source of arXiv:2606.12188 on 2026-09-12).**

- *(T1)* The Grassmannian subsection `grassman`, the first Lemma of section
  `schubert` and the telescoping remark of section `sec:simple-example`. Every
  stage pair `(p_n, q_n)` is totally degeneracy-forcing: every bundle map
  `p_n -> q_n` over `X_n` vanishes at some point.
- *(T2)* `prop:sparse-simplefication-survival`:
  - `psi_n = psi_n^top direct_sum psi_n^pt`, where `psi_n^pt` is a finite sum
    of point evaluations;
  - with `E_(n,m)` the top-summand projection,
    `E psi_(m,n)(p_m) E = p_n`, and `E` reduces `psi_(m,n)(p_m)`, so
    `p_n <= psi_(m,n)(p_m)`, and similarly `q^_n <= psi_(m,n)(q^_m)`;
  - `rank(q_n)/rank(s_n) = prod_(r < n) alpha_r`, with `s_1 = q_1`;
  - the connecting maps are injective, hence isometric.
- *(Br)* The branch traces of `doubling-ah-finite-stage-continuous-ranks-constant-proof`,
  Step 1, with constant contamination:
  - for `x in X_n` there is a trace `sigma_x` whose stage-`n` measure is
    `beta_n delta_x + kappa_n`, with `beta_n = prod_(r >= n) alpha_r` and
    `kappa_n` independent of `x`;
  - so `d_(sigma_x)(b) >= beta_n rank b(x) / rank(s_n)` for
    `b in M_K(B_n)_+`;
  - `sigma_x` is extreme by Lemma 1 of
    `research/artifacts/tw-doubling-poulsen-and-comparison-2026-09-12.md`, since
    `beta_N -> 1`.

**Step 1: reduce to one finite stage.**
- Let `c = [c_0]`. The class `[p_m]` is compact, so `[p_m] << c`, and there is
  `eps > 0` with `[p_m], [q^_m] <= [(c_0 - eps)_+]`.
- Choose `N` and `b in M_K(B_N)_+` with `||b - c_0|| < eps/2`. Put
  `b' = (b - eps/2)_+`. Rordam's lemma gives
  `(c_0 - eps)_+ <~ b' <~ c_0`, so `[p_m], [q^_m] <= [b'] <= c`.
- For a projection `p`, `p <~ b'` gives `r` with `||p - r b' r*|| < 1/4`.
  Approximate `r` at a finite stage. Because the maps are isometric, there is a
  stage `n >= N` with `||psi(p_m) - r_0 psi(b') r_0*|| < 1/2`, and the same for
  `q^_m` with some `r_1`.
- Rordam's lemma and `(p - 1/2)_+ ~ p` then give, in `M_infinity(B_n)`,
  `psi_(m,n)(p_m) <~ b''` and `psi_(m,n)(q^_m) <~ b''`, where
  `b'' = psi_(N,n)(b')`. By (T2), `p_n <~ b''` and `q_n <~ b''`.

**Step 2: orthogonal copies at one point.**
- Every `x in X_n` has `rank b''(x) <= K rank(s_n)`.
- For a projection `p` with `p <~ b''`:
  - choose `y` with `||p - y* b'' y|| < 1/2`;
  - put `s = p y* b'' y p`, which is invertible in `p M p`, and set
    `y_1 = y p s^(-1/2)`;
  - then `y_1* b'' y_1 = p`;
  - `v = b''^(1/2) y_1` satisfies `v*v = p`, and `p' = vv*` is a projection in
    the hereditary subalgebra of `b''`.
- Do this for `p_n` and for `q_n`, obtaining `v, w` with `v*v = p_n`,
  `w*w = q_n`, and `p' = vv*`, `q' = ww*` hereditary under `b''`. All of this
  happens inside `C(X_n) tensor K`.
- The section `T(x) = w(x)* v(x)` is a bundle map `p_n -> q_n`. By (T1) there is
  `x_0` with `T(x_0) = 0`.
- Then `q'(x_0) p'(x_0) = w (w* v) v* (x_0) = 0`.
- The ranges of `p'(x_0)` and `q'(x_0)` lie in the range of `b''(x_0)`, because
  both projections are hereditary under `b''`. So
  `rank b''(x_0) >= rank p_n + rank q_n = 2 d_n`.

**Step 3: read the rank at the branch trace.** By (Br),

```text
d_(sigma_(x_0))(c) >= d_(sigma_(x_0))(b') >= beta_n (2 d_n) / rank(s_n)
                    = 2 beta_n prod_(r < n) alpha_r
                    = 2 t_m prod_(r >= m) alpha_r,
```

using `d_n / rank(s_n) = prod_(r < n) alpha_r` and
`t_m = prod_(r < m) alpha_r`. Since `prod_(r >= m) alpha_r >= delta > 1 - eta`,
the theorem follows.

**Step 4: the slice-wise form.**
- *Setup.* By the construction in section `nonsimpleconstruction` and the
  telescoping of `sec:simple-example`, `X_n` is a product over leaves `l in L`
  of copies of `X_m`, times projective factors. Each top leaf map `lambda_l` is a
  coordinate projection. The leaf-`l` summand of `psi_(m,n)(p_m)` is
  `E_l = lambda_l^* p_m tensor gamma_l` for a line bundle `gamma_l` pulled back
  from the projective factors, and similarly `F_l = lambda_l^* q_m tensor gamma_l`.
  So `Hom(E_l, F_l) = lambda_l^* Hom(p_m, q_m)`.
- *Every slice sees a zero.* Fix a slice `S`. Let `iota: X_m -> X_n` insert `x`
  into coordinate `l` with the other coordinates fixed, so
  `lambda_l o iota = id`. Then `iota^* E_l = p_m` and `iota^* F_l = q_m` up to the
  trivial line `iota^* gamma_l`. For a bundle map `T: E_l -> F_l`, `iota^* T` is a
  bundle map `p_m -> q_m` over `X_m`, and by (T1) it vanishes at some point. So
  every bundle map `E_l -> F_l` vanishes at some point of `S`.
- *Run the proof.* Steps 1 and 2 apply verbatim with `(p_n, q_n)` replaced by
  `(E_l, F_l)`, which are subprojections of `psi_(m,n)(p_m)` and
  `psi_(m,n)(q^_m)`. They give a zero `x_0 in S` of `w* v` and
  `rank b''(x_0) >= 2 rank(E_l) = 2 d_m`. Step 3 gives
  `d_(sigma_(x_0))(c) >= 2 beta_n d_m / rank(s_n) = 2 beta_n t'`.
- *Directedness.* If `min f > t'`, the compact classes `[E_l]` and `[F_l]` lie
  in `L'_f`. If also `f < 2 beta_n t'` along a slice, any `c` with `d(c) <= f`
  above both would contradict the bound at `x_0 in S`.

**Corollary.** The directedness argument is spelled out in the target. Thiel's
lemma is the upward-directedness lemma for `L'_f` that immediately precedes
`dfn:alpha` in section `sec:rankCu` of arXiv:1711.04721. Its standing hypotheses
were read verbatim at the head of that section on 2026-09-12. Square.
