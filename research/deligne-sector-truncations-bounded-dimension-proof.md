---
rg: 2
id: deligne-sector-truncations-bounded-dimension-proof
kind: route
title: Property (T) of the cover lattice, Malcev and Deligne's finite residual bound every sector truncation
target: deligne-sector-truncations-have-bounded-dimension
requires:
  - kazhdan-reps-without-fd-subreps-have-linear-subspace-boundary
  - deligne-universal-cover-lattice-is-non-rf-kazhdan
  - deligne-covers-of-sp2g-z-have-finite-residual-2z
  - finitely-generated-linear-groups-are-residually-finite
---

Notation of the target.

**Step 0: property (T).** By `deligne-universal-cover-lattice-is-non-rf-kazhdan` the preimage
`Gamma~` of `Sp_(2g)(Z)` in the universal cover has property (T) for `g >= 2`. The connected
`n`-fold cover is the quotient of the universal cover by `<z^n>`, so `Gamma_n = Gamma~ / <z^n>` is a
quotient of a Kazhdan group and is Kazhdan. It is finitely generated, so the finite generating set
`S cup {z}` has a Kazhdan constant `kappa_n > 0`.

**Step 1: no finite-dimensional sector subrepresentation.** Let `sigma` be a nonzero
finite-dimensional subrepresentation of `pi`, so `sigma(z) = zeta I`. The group `sigma(Gamma_n)` is
finitely generated and linear, hence residually finite
(`finitely-generated-linear-groups-are-residually-finite`). Since `sigma(z^2) = zeta^2 I != I`,
some finite quotient `f` of `sigma(Gamma_n)` has `f(sigma(z^2)) != 1`. Then `ker(f o sigma)` is a
finite-index normal subgroup of `Gamma_n` not containing `z^2`, against `Res_fin(Gamma_n) = <z^2>`
(`deligne-covers-of-sp2g-z-have-finite-residual-2z`).

**Step 2: the boundary inequality.** By Step 1, `pi` satisfies the hypothesis of
`kazhdan-reps-without-fd-subreps-have-linear-subspace-boundary` with `Q = S cup {z}`. Since
`pi(z) W = W`, the letter `z` contributes `e_z(W) = 0`, so the maximum is attained on `S`.

**Step 3: truncation bound.** For `w` in `W_s`, `pi(s) w = rho(s) w` lies in `W`, so
`pi(s) W_s <= W n pi(s) W` and `e_s(W) <= codim_W W_s <= B`. Step 2 gives
`kappa_n^2 dim W / 2 <= B`.

**Step 4: truncations have bounded-rank defects.** The inverse `rho(s)^(-1)` agrees with
`pi(s)^(-1)` on `rho(s) W_s`, which also has codimension at most `B` in `W`, and `rho(z) = pi(z)` on
all of `W`. For a relator `r = t_1 ... t_L`, let `V_r` be the set of `w` with `w` in the agreement
subspace of `t_L`, `rho(t_L) w` in that of `t_(L-1)`, and so on. Each condition is the preimage of a
subspace of codimension at most `B` under an invertible map, so `codim V_r <= L B`. On `V_r`,
`rho(r) w = pi(r) w = w`, since `r` is a relator. So `rank(rho(r) - I) <= codim V_r <= L B`.

**Step 5: the equivalence remark.** If every rank-`k` sector tuple has `dim W <= D(k)`, embed `W`
isometrically into the sector representation induced from the character `z -> zeta` of `<z>`, which
is infinite-dimensional, and take `W_s = 0`. That is a `D(k)`-truncation. Conversely, a truncation
constant `C(k)` gives `dim W <= 2 C(k) / kappa_n^2` by Step 3. ∎
