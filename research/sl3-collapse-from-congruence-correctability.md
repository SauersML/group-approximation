---
rg: 2
id: sl3-collapse-from-congruence-correctability
kind: route
title: Correct the lattice microstates into the closed sector and let the Weyl evaluation finish
target: sl3-pair-relative-commutant-route
requires:
  - odd-congruence-lambda-exact-sector-collapses
  - sl3z-regular-microstates-are-congruence-correctable
---

Let `M`, `pi`, `k in pi(Lambda)' cap M` be as in `(RC3)`, with
microstates `(sigma_m, V_m, k_m)`.  The `Lambda`-part `sigma_m` is
asymptotically multiplicative with asymptotically regular trace, so
`sl3z-regular-microstates-are-congruence-correctable` replaces it by
genuine odd-congruence (projective) representations `rho_m` within
vanishing normalized-HS distance (after a vanishing-proportion corner,
absorbed into the ultraproduct).  The resulting representation `pi'`
of `Gamma` -- same `V`, corrected `Lambda`-slot -- is
`Lambda`-exact of odd congruence type and agrees with `pi` in the
ultraproduct, so `pi(Lambda)' cap M = pi'(Lambda)' cap M` and
likewise for `Gamma`.

Apply `odd-congruence-lambda-exact-sector-collapses` to `pi'`.  In
the projective case the corrector evaluation yields `W` scalar
rather than `W = 1`; since the collapse argument only uses
`[k, W] = 0`, scalars suffice, and perfectness of `SL_3(Z)`
(`projective-far-defect-formula`, part 1) removes even the scalar if
an exact statement is wanted.  Either way every `k in
pi(Lambda)' cap M` commutes with `pi(h)`, hence with `pi(Gamma)`:
this is `(RC3)`, the statement of the target.

Position in the lane: this is the fourth independent last-missing
input for the higher-rank collapse, and the first whose open half is
a statement about the LATTICE alone (no ambient ultraproduct, no
S-arithmetic group, no transfer inequality): a correctability
property of `SL_3(Z)` microstates at congruence targets, sitting
exactly one hyperfiniteness relaxation beyond the in-graph
character-rigidity stability theorem.
