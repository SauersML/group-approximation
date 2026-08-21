---
rg: 2
id: sl3-collapse-from-projective-transfer
kind: route
title: In the ultraproduct the projective transfer loses its phase to perfectness and yields the exact collapse
target: sl3-pair-relative-commutant-route
requires:
  - projective-trace-square-transfer-for-sl3-pair
  - projective-far-defect-formula
---

Let `M` be a tracial matrix ultraproduct, `pi` a trace-preserving
regular-trace representation of `A = SL_3(Z[1/2])`, and `k` a unitary
of `pi(C)' cap M`, `C = SL_3(Z)`.  Lift to microstates: unitaries
`k_m in U(d_m)` and assignments `rho_m` with presentation defect
`delta_m -> 0` along the ultrafilter, with `max_(c in S_C)
|| [k_m, rho_m(c)] ||_2 -> 0`, hence

```text
1 - |tr([k_m, rho_m(c)])|^2 -> 1 - |tau([k, pi(c)]-word)|^2 = 0
```

for every `c in S_C` (exact commutation gives the word trace `1`).
Apply `(PTS1)` of `projective-trace-square-transfer-for-sl3-pair` at
each level and pass to the limit: `|tau(k^* pi(h)^* k pi(h))| = 1`
with `h = diag(2, 1, 1/2)`.  Cauchy--Schwarz equality of unit vectors
up to phase gives `k pi(h) = omega_h pi(h) k` for some
`omega_h in T`: the commutator `[k, pi(h)]` is exactly scalar in the
limit.

Now the phase dies.  `k` commutes exactly with `pi(C)` and
projectively with `pi(h)`; since `A = <C, h>`, the map
`gamma |-> k pi(gamma) k^* pi(gamma)^*` is scalar on all of `A` and
multiplicative (part 1 of `projective-far-defect-formula`, applied
with `Lambda = A`), hence a character `omega : A -> T`.
`SL_3(Z[1/2])` is perfect, so `omega = 1` and `k in pi(A)' cap M`.
Unitaries span, so `pi(C)' cap M subseteq pi(A)' cap M`; the reverse
is automatic.  This is `(RC3)`, the statement of the target.

Two remarks the formula adds beyond the phase algebra.  First, the
same conclusion follows from the far side alone: scalar commutation
with every `pi(gamma)` makes the doubled vector invariant, so
`s_proj = 1`, and part 4 of the formula gives exact centrality --
the route is robust to how the scalar information arrives.  Second,
the formula classifies the enemy of the required transfer claim: a
failure of `(PTS1)` along regular microstates is a `c_0` spherical
component of the doubled adjoint representation with far energy
`1 - s_proj`, contractible by the doubled lazy Hecke average at the
explicit rate `delta_0(3, 2)` -- so quantitative work on the transfer
inequality may assume the enemy's geometric decay profile from the
start.

Together with `non-hyperlinear-from-sl3-relative-commutant-collapse`
this makes the projective transfer hole a third independent
last-missing input for the higher-rank goal edge, alongside
`single-hecke-average-isometry-for-lambda-central-unitaries` and
`hnn-carrier-factorial-character-collapse`.
