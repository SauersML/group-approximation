---
rg: 2
id: corona-corner-detection-criterion-proof
kind: route
title: Run transport inside an arbitrary commutant corner and cut the spectrum
target: corona-corner-detection-criterion
requires: [kazhdan-asymptotic-commutant-transport]
artifacts:
  - non_mf_groups_exist.tex
---

## Why sufficient

**Clause 1.**  The central-corner reduction of the manuscript
(`sec:transport`, the paragraph before `thm:sign-criterion`) needs only
that `q` be a nonzero projection commuting with `Theta(H)`: a spectral cut
at `1/2` of a self-adjoint lift gives coordinate projections `(q_n)`,
`r_n = rank q_n` is positive on an infinite set, and `q Q q` is again a
norm matrix corona with unit `q`, on which `Theta_q(g) = q Theta(g) q` is a
homomorphism with unitary coordinate lifts.  Nothing there uses `eps`.

Inside that corner, `c` still centralizes `iota(Gamma)` and `t` still
compresses it, because these are identities in `H` and `Theta_q` is a
homomorphism.  So `Theta_q(c)` is an asymptotic commutant of
`Theta_q(iota(Gamma))`, `kazhdan-asymptotic-commutant-transport` puts
`Theta_q(d) = Theta_q(t) Theta_q(c) Theta_q(t)^-1` there as well, and
therefore `u ~_2 q` **in the corner's normalized Hilbert--Schmidt norm**.
For unitaries, `‖ab - 1‖_2 <= ‖a - 1‖_2 + ‖b - 1‖_2`, `‖a^-1 - 1‖_2 = ‖a - 1‖_2`,
and the normalized `2`-norm is conjugation invariant, so
`{x : ‖Theta_q(x) - q‖_2 = 0}` is a normal subgroup of `H`; it contains `u`,
hence the whole normal closure of `u`, hence `eps = u^2`.

**Clause 2.**  Let `S` be a clopen subset of `sp(Theta(eps))` with
`1 not in S`.  Then `1_S` is continuous on the spectrum, so
`q = 1_S(Theta(eps))` lies in `C*(Theta(eps))`; since `eps` is central in
`H`, `Theta(eps)` commutes with `Theta(H)`, hence so does `q`.  If `S` is
nonempty then `q != 0`, and `delta = dist(1, S) > 0` gives
`(q Theta(eps) q - q)^* (q Theta(eps) q - q) >= delta^2 q`, so
`‖q Theta(eps) q - q‖_2 >= delta` because the corner trace is normalized
(`tau_q(q) = 1`).  This contradicts clause 1, so `S` is empty.  A nonempty
closed subset of the circle with no nonempty clopen piece missing `1`
contains `1` (take `S` to be the whole spectrum) and is connected (a
disconnection has a clopen piece missing `1`).

**Clause 3.**  Given such `q` and `lambda`, put `eta = ‖(Theta(eps) - lambda) q‖`.
In the corner, `‖q Theta(eps) q - lambda q‖ <= eta`, so
`‖q Theta(eps) q - q‖_2 >= |lambda - 1| - eta > 0`, contradicting clause 1
unless no such pair exists.  A unitary whose spectrum is `{1}` is `1`;
combined with clause 2, if `Theta(eps) != 1` then `sp(Theta(eps))` contains
a point `lambda` with `|lambda - 1| > 0`, and clause 3 says no commutant
projection localizes there.  For `eps` of order `n` the spectrum lies in
the `n`-th roots of unity, so it is finite; being connected it is `{1}`,
i.e. `Theta(eps) = 1`, which is `central-sign-corona-obstruction` (there
`n = 2` and `q = (1 - Theta(eps))/2`).
