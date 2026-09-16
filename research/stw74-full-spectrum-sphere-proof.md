---
rg: 2
id: stw74-full-spectrum-sphere-proof
kind: route
title: Left-invertible witnesses in a projectionless hereditary subalgebra force full spectra and projectionless supports
target: stw74-two-level-failure-has-full-spectrum-sphere
requires:
  - stw74-all-stabilized-projections-are-properly-infinite
  - stw74-simple-infinite-projections-are-properly-infinite
  - stw74-lxxiv-hinge-is-two-level-descent
artifacts:
  - research/artifacts/stw74-two-level-descent-2026-09-16.md
---

Full proof: Section 3 of the artifact (with Lemmas 1, 2, 4, K, R of
Section 1).

* **Lemma K.**  If `H` is hereditary, `zz* in H` and `z*z` is invertible,
  then `z(z*z)^(-1)z* = h X^2 h` with `h=zz*`, `X=z(z*z)^(-2)z*`, is a
  nonzero projection in `H`.
* **Lemma R.**  If `zz* in H` then `zXz* in H` for all `X`, via
  `h_n=h(1/n+h)^(-1)` and `||z-h_n z||^2<=1/(4n)`.
* **Lemma 4.**  A nonzero properly infinite projection `q` in a unital simple
  algebra has `w` with `w*w=1`, `ww*<=q`.

Item 1: `M_2(A)` is simple; the projection `p in M_2(H)` is properly
infinite in `A tensor K` (first required claim) with witnesses in
`pM_2(A)p`; Lemma 4 in `M_2(A)` gives an isometry `u` with `uu*<=p`, and
`v=u epsilon_1=(x,y)^T` has `v*v=1`, `vv* in pM_2(A)p subset M_2(H)`.

Item 2: `b_xi=xi*(vv*)xi in H`, `e_xi=v*(xi xi*)v`, so `e_xi+e_eta=v*v=1`.
Lemma K makes every `e_xi` non-invertible, so `0,1 in sigma(e_xi)`; a gap
in `(0,1)` would give a nonzero spectral projection of `b_xi` in `H`.

Item 3: a projection in `Her(e_xi)` is properly infinite (second required
claim), so Lemma 4 gives an isometry `w` with `ww*` in `Her(e_xi)`;
approximate units `min(1,n e_xi)<=n e_xi` show `w* e_xi w>=1/(2n)` is
invertible, and `z_xi w` then has `(z_xi w)(z_xi w)* in H` (Lemma R) and
invertible `(z_xi w)*(z_xi w)`, so Lemma K gives a projection in `H`.

Dichotomy: the forward direction is immediate from (SP) (and `Her(1)=A`);
conversely, if (SP) fails, the "moreover" clause of the third required
claim produces `H` as in the hypothesis, and item 3 for `xi=(1,0)`,
`eta=(0,1)` gives `e=x*x` with `Her(e)`, `Her(1-e)` projectionless.
