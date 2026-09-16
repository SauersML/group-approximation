---
rg: 2
id: sln-z-thin-quasiregular-not-weakly-in-fd-proof
kind: route
title: Kazhdan projection plus Bourgain-Varju gap on congruence quotients bounds x below one, while the thin coset vector is fixed
target: sln-z-thin-quasiregular-not-weakly-contained-in-fd
requires: [sln-z-thin-codense-tau-pair]
artifacts:
  - research/artifacts/sl4z-thin-corona-gap-reduction-2026-09-16.md
---

The artifact, Sections 1--4, gives the full proof.

1. **Uniform gap (KF).**
   - By `sln-z-thin-codense-tau-pair`, every finite-dimensional unitary representation
     `rho` of `Gamma` factors through a congruence quotient `SL_n(Z/m)`, and
     `pi_m(C) = SL_n(Z/m)`.
   - Bourgain--Varju expansion of `Cay(SL_n(Z/m), pi_m(F))`, uniform in `m`, gives
     `sum_(c in F) ||rho(c) xi - xi||^2 >= kappa^2 ||xi||^2` on the orthogonal complement
     of the invariant vectors.  The steps are the discrete Cheeger inequality, Peter--Weyl,
     and summation over isotypic components.
2. **Kazhdan projection.**
   - Property (T) gives `kappa_S > 0` for `S`, so `nu^N` converges to a central projection
     `p` with `rho(p)` the projection onto `Gamma`-invariant vectors in every representation.
   - Hence `rho(x)` is `rho(mu)` on the complement of the invariants and `0` on them.
   - (Q): `<rho(mu) xi, xi> = ||xi||^2 - (4|F|)^(-1) sum_c ||rho(c) xi - xi||^2`.
3. **Item 1.**  Combine 1 and 2: `||rho(x)|| <= 1 - kappa^2/(4|F|)`.
4. **Item 2.**  `C` has infinite index, so `l^2(Gamma/C)` has no nonzero invariant vector
   and `sigma_C(p) = 0`.  The coset vector `delta_C` is fixed by `C`, so
   `sigma_C(x) delta_C = sigma_C(mu) delta_C = delta_C`.  Also `||x|| <= ||mu|| <= 1`.
5. **Consequences.**
   - Weak containment is norm domination on `C*(Gamma)`.
   - An RFD `C*(Gamma)` would have `||x|| = sup_rho ||rho(x)|| <= 1 - epsilon`, while
     `||x|| >= ||sigma_C(x)|| = 1`.
