---
rg: 2
id: toms-leaf-average-rank-via-overlap-window-cubes
kind: route
title: If overlap-window cubes force linear depth, every realizer of a leaf-average rank has eps_M bounded below by c/(2 d_n), so none exists
target: toms-simple-algebra-realizes-no-leaf-average-rank
requires: [toms-overlap-window-cubes-force-linear-depth, toms-transit-windows-fill-unless-their-ranks-overlap]
---

This is one direction only: the conjecture implies the target. The converse is not claimed.

Suppose `a` realizes `tau(h)`, with `h` non-constant. As in
`toms-simple-algebra-has-no-block-diagonal-rank-realizer`, write `a` as the supremum of a
Cuntz-increasing sequence `a_m` of stage elements, with `d(a_m) <= f` and
`eps_m = sup (f - d(a_m)) -> 0`. The argument below is written for `A`. For `B`, replace
`d_n` by `r_n / beta_n`, as in the target's last paragraph.

1. *Choose the stage.* Fix a swap path `x` in `X_n` with `phi(s) + phi(1-s) = c`, and
   `w > 0` with `phi(1/2 + w) - phi(1/2) = delta > 0` independent of `n`. Such paths are
   those of `toms-sibling-cube-swap-drops-add-to-depth-n`. Take `n` so large that
   `eps_n + 1/(2 d_n) < delta`.
2. *Windows.* By Part 5 of `toms-transit-windows-fill-unless-their-ranks-overlap`, the window
   `[1/2 - w, 1/2 + w]` has `kappa >= 1` at every one of the `N = K/2` bottom sibling nodes,
   for every `M > n`.
3. *Apply the conjecture to `a_M`.* On the box, `psi_(n,M)(a_n) <~ a_M` and
   `rank a_M <= floor(d_M f) = U`. So `toms-overlap-window-cubes-force-linear-depth` gives a
   point where `rank a_M <= U - cN`.
4. *Lower band.* At that point `d_M (f - eps_M) <= rank a_M <= d_M f - cN`. So
   `eps_M >= cN / d_M = c / (2 d_n)`, since `d_M = K d_n`.
5. *Contradiction.* `n` is fixed and `M -> infinity`, so `eps_M -> 0` contradicts the bound
   `eps_M >= c / (2 d_n) > 0`.

**Integrality.** The conjecture is stated with `D = d_n c` an integer. If the swap paths
available at stage `n` do not give an integer `d_n c`, step 3 needs the conjecture in the
variant with `U = floor(N D)`. Part 5 still gives `kappa >= 1` there, and steps 4 and 5 are
unchanged. The variant is part of the open statement; this route does not prove it.
