---
rg: 2
id: jensen-helly-graphs-have-contractible-rips-complexes-proof
kind: route
title: Jensen barycentres plus Helly number k+1 plus rounding verify Zaremsky's criterion at every t ≥ k(k+1)
target: jensen-helly-graphs-have-contractible-rips-complexes
requires:
  - zaremsky-rips-contractibility-criterion
artifacts:
  - research/artifacts/zp-raag-rips-products-of-trees-2026-09-13.md
---

This is §3 of the artifact, with Lemmas J, H and R replaced by properties
(J), (H) and (R).

Property (*) of the criterion holds: distances are integers, and bounded
degree bounds the size of any set of diameter `t`. Fix an integer
`t ≥ k(k+1)` and put `r_t = kt/(k+1) + k/2`. Then `r_t < t`, and
`r_t ≤ t − k/2`.

1. **Averaging.** For vertices `s_1..s_p` and `μ` uniform on them, (J) gives
   `d(s_j, b) ≤ ((p−1)/p) · max_l d(s_j,s_l)` and
   `d(z, b) ≤ (1/p) Σ_l d(z, s_l)` for every vertex `z`.
2. **Enclosing balls.** Let `diam S = t`. Any `p ≤ k+1` of the balls
   `B(s, kt/(k+1))`, `s ∈ S`, contain the barycentre of their centres, since
   `(p−1)/p ≤ k/(k+1)`. By (H) all of them meet at some `c`, and (R) gives a
   vertex `y` with `d(s,y) ≤ r_t` for all `s ∈ S`. So the centre set
   `Y(S) = {y ∈ V : d(y,s) ≤ r_t ∀ s}` is nonempty.
3. **Central centre.** Consider the finite family `B(s, kt/(k+1))` for
   `s ∈ S` and `B(y, t − k/2)` for `y ∈ Y(S)`. A subfamily of at most `k+1`
   members with `p ≥ 1` members of the first kind contains the barycentre of
   those `s`: by (1) it is within `kt/(k+1)` of each such `s`, and within
   `r_t ≤ t − k/2` of each such `y`. A subfamily with only members of the second
   kind contains any `s ∈ S`. By (H) all members meet at some `c`. Rounding by
   (R) gives `y_0` with `d(s,y_0) ≤ r_t` for all `s`, so `y_0 ∈ Y(S)`, and
   `d(y, y_0) ≤ t` for all `y ∈ Y(S)`.
4. The criterion then gives `VR_{t_0}(V)` contractible for every integer
   `t_0 ≥ k(k+1) − 1`.
