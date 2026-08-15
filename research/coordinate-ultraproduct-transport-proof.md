---
rg: 2
id: coordinate-ultraproduct-transport-proof
kind: route
title: Kazhdan projection and one-sided compression on the coordinate ultraproduct
target: coordinate-ultraproduct-transport
requires: []
artifacts:
  - non_mf_groups_exist.tex
---

## Why sufficient

**Clause 1.**  `‖U_n(g) U_n(h) - U_n(gh)‖_op -> 0` means the defect is
`omega`-null, so on `H_omega = prod_omega C^{d_n}` the induced unitaries
compose exactly: `tilde U(g) tilde U(h) = tilde U(gh)`.  This is an honest
unitary representation of `H`.  The natural action of
`A_omega = prod_omega M_{d_n}` on `H_omega` is isometric and faithful —
choose coordinate unit vectors almost attaining the operator norms, as in
the manuscript's argument for `B_omega` — so
`‖tilde U(h) - 1‖ = lim_omega ‖U_n(h) - 1‖_op`, which is the corona
operator norm.

**Clause 2.**  `tilde U circ iota` is an honest unitary representation of
`Gamma`, so its integrated form is a `*`-homomorphism
`C^*_max(Gamma) -> A_omega`; the image `P` of the Kazhdan projection
(Bekka--de la Harpe--Valette, as used in the manuscript's transport proof)
is the projection onto the invariant vectors of that representation, and it
lies in `A_omega`.  Being an invariant projection,
`P` commutes with `tilde U(iota(Gamma))`; `c` centralizes `iota(Gamma)`, so
`tilde U(c)` preserves the invariant subspace and its orthocomplement and
therefore commutes with `P`.  For `V = tilde U(t)`, one-sided compression
gives

    P H_omega = H_omega^{iota(Gamma)} <= H_omega^{t iota(Gamma) t^-1} = V P H_omega,

so `P <= V P V^*`.  `A_omega` is finite: if `v^* v = 1`, polar correction
replaces a representing sequence by unitaries along `omega`, so `v v^* = 1`.
The manuscript's cancellation then upgrades `P <= VPV^*` to `P = VPV^*`;
hence `PV = VP` and `P` commutes with `tilde U(t)`, so with all of `H_0`.

**Clause 3.**  `tilde U(d) = V tilde U(c) V^*` commutes with `P`, and
`tilde U(iota(gamma)) P = P` for all `gamma`.  Therefore

    tilde U(u) P = tilde U(d) tilde U(iota(a)) tilde U(d)^-1 tilde U(iota(a))^-1 P
                 = tilde U(d) tilde U(iota(a)) tilde U(d)^-1 P
                 = tilde U(d) tilde U(iota(a)) P tilde U(d)^-1
                 = tilde U(d) P tilde U(d)^-1 = P.

So `tilde U(u)` fixes `ran P` pointwise.  The set
`{h in H_0 : tilde U(h) P = P}` is a subgroup, and it is normal in `H_0`
because every `tilde U(h)` with `h in H_0` commutes with `P`; it contains
`u`, hence the normal closure of `u` in `H_0`, hence `eps = u^2`.
