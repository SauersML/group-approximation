---
rg: 2
id: soelberg-support-pair-has-no-rational-units
kind: claim
title: No nontrivial unit of Q[S] or Z[S] lives on Gardam's Soelberg support pair, and no eighth-root signed-monomial unit does either
distinct_from:
  gardam-support-pair-has-no-rational-units: that classifies units on Gardam's 21-element pair in the Promislow group P, where complex units exist; this is the 29-element pair of the Soelberg group S, a different group, and it uses the definite shadows of S as linear constraints rather than an unconstrained Groebner basis.
  soelberg-gardam-unit-has-no-integral-lift: that excludes integral units reducing to Gardam's F_2 unit at every support; this excludes every nontrivial rational unit on the fixed pair (A, B), including units congruent to trivial units modulo 2, which the shadow argument alone does not touch.
  rational-unit-conjecture-torsion-free: that is the unit conjecture over Q for every torsion-free group; this is one support pair on one group.
  integral-unit-conjecture-torsion-free: that is Higman's conjecture for every torsion-free group; this is one support pair on one group.
artifacts:
  - experiments/soelberg-unit-lifting-2026-09-17/soelberg_engine.py
  - experiments/soelberg-unit-lifting-2026-09-17/soelberg_definite_shadows.py
  - experiments/soelberg-unit-lifting-2026-09-17/build_system.py
  - experiments/soelberg-unit-lifting-2026-09-17/pair_shadow_classification.py
  - experiments/soelberg-unit-lifting-2026-09-17/run_all_msolve.sh
  - experiments/soelberg-unit-lifting-2026-09-17/calibrate_pair_shadow.py
  - experiments/soelberg-unit-lifting-2026-09-17/signed_monomial_sat.py
  - experiments/soelberg-unit-lifting-2026-09-17/calibrate_promislow.py
  - experiments/soelberg-unit-lifting-2026-09-17/logs/build_system.log
  - experiments/soelberg-unit-lifting-2026-09-17/logs/pair_shadow_classification.log
  - experiments/soelberg-unit-lifting-2026-09-17/logs/calibrate_pair_shadow.log
  - experiments/soelberg-unit-lifting-2026-09-17/logs/signed_monomial_sat.log
  - experiments/soelberg-unit-lifting-2026-09-17/logs/signed_monomial_sat_full.log
  - experiments/soelberg-unit-lifting-2026-09-17/logs/calibrate_promislow.log
---

**ESTABLISHED (computer-assisted; trust surface in the route).** Let `S` be
the Soelberg group, and let `A` and `B` be the 29-element lists of words that
support Gardam's unit `nu in F_2[S]` and its inverse (arXiv:2312.05240v2,
Theorem B, ancillary file). Their order is as in `soelberg_engine.py`.

1. **Rational pair classification.** Let `U` be a unit of `Q[S]` with
   `supp(U) in A` and `supp(U^-1) in B`. Then `U = lambda g` with
   `lambda in Q^x` and `g in A`. The same holds for `Z[S]`, and for `Z_(p)[S]`
   for every prime `p`.
2. **Eighth-root signed-monomial units.** Let `alpha, beta` be roots of unity
   with `alpha^4, beta^4 in {+-1}`, and write `ex(w)`, `ey(w)` for the
   exponent sums of a word. No unit of `Z[alpha, beta][S]` has the form

       u = sum_k eps_k alpha^ex(A_k) beta^ey(A_k) A_k,
       u^-1 = sum_l del_l alpha^ex(B_l) beta^ey(B_l) B_l,

   with `eps, del in {0, +-1}` and `|supp u| >= 2`. This is the shape of
   Gardam's complex unit on `P`. The same encoding, run on Gardam's `P` pair,
   finds solutions exactly in the class `(alpha^4, beta^4) = (-1, -1)`, where
   that unit lives.

**What this rules out.** Case A of Higman's conjecture on `S` asks for units
congruent modulo 2 to a trivial unit. The shadow argument of
`soelberg-gardam-unit-has-no-integral-lift` does not see Case A. Item 1 closes
both cases on the one support pair that carries the only known nontrivial
`F_2`-unit of `S`. So on `S`, as on `P`, the known characteristic-2 unit does
not come from characteristic zero on its own pair.

On `P` the pair does carry complex units, 16 of them over `Qbar`. On `S`,
item 2 excludes their mechanism: a `Z/8`-graded sign pattern. No
characteristic-zero unit of `S` is known on any support.

**Scope.** This is one fixed support pair. It gives no bound on supports of
units of `Q[S]` in general. Units over `Qbar` on `(A, B)` that are not
signed-monomial are not classified here. The shadows constrain only rational
units, since `D(R)` has non-monomial units.

DERIVATION
[[soelberg-support-pair-has-no-rational-units-proof]]
