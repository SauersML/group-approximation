---
rg: 2
id: ghb7-congruence-kernel-flexibly-hs-stable
kind: claim
title: The torsion-free congruence kernel of GHB_2(7) is flexibly Hilbert--Schmidt stable
distinct_from:
  kazhdan-hyperbolic-b2-group-flexibly-hs-stable: that is the existential premise over all hyperbolic Kazhdan groups with b_2 >= 1; this is one explicit instance, the kernel H of the SL_4(F_7) quotient of GHB_2(7)
  sln-z-flexibly-hs-stable: that asks flexible HS stability of an integral lattice, which is residually finite and hyperlinear, so its stability is calibrated against goodness; this asks it for a torsion-free hyperbolic kernel whose residual finiteness and hyperlinearity are both unknown
---

**OPEN.** Let `H = Ker(ψ)` be the torsion-free finite-index kernel of the quotient
`ψ : G_{HB_2}(7) → SL_4(F_7)` from `ghb7-congruence-kernel-hyperbolic-kazhdan-with-large-b2`.
The claim is that `H` is flexibly Hilbert--Schmidt stable in the Dogon--Vigdorovich
sense: every asymptotic representation `σ_n : H → U(d_n)` in normalized HS norm is
close, after enlarging the dimension, to genuine representations.

**If true.** `H` is hyperbolic, Kazhdan, with `b_2(H;Q) >= 1380`. So
`kazhdan-hyperbolic-hs-stability-kills-hyperlinearity` gives a non-hyperlinear
hyperbolic finite central extension of `H`, which is a nonsofic and
non-residually-finite hyperbolic group.

## Attempts

- **Calibration (proved on main).**
  - If `H` is hyperlinear, stability forces a persistent prime degree-two class on a
    finite-index subgroup of `H`, i.e. `H` is not good
    (`hs-stable-hyperlinear-kazhdan-hyperbolic-forces-persistent-class`). A proof for a
    hyperlinear `H` therefore contains a profinite statement of Gromov-question strength.
  - If `H` is not hyperlinear, that alone answers `non-hyperlinear-group`.
- **Strict stability is excluded.** Becker--Lubotzky rule out same-dimension HS stability
  for infinite hyperlinear Kazhdan groups (`infinite-hyperlinear-kazhdan-group-is-not-hs-stable`).
  Only the flexible notion can hold.
- **Class-wide arguments are screened.** Any argument that works for a class closed under
  Belegradek--Osin covers already makes the binary Leavitt unit group non-hyperlinear
  (`classwide-hyperbolic-kazhdan-hs-stability-covers-fp-kazhdan`). A proof for `H` must use
  features specific to `H`:
  - the free cocompact action on a CAT(−1) triangle complex with links the coset graphs
    of `U_3(7)` and `U_4(7)`;
  - the EJZ angles compiled in `Kazhdan/EJZAngleGHB.lean`;
  - the explicit finite aspherical `K(H,1)`.
- **No known template.** No source read in this lane exhibits a flexibly HS stable
  infinite property (T) group. Dogon--Vigdorovich's target `SL_2(Z[1/p])` has (T;FD) but
  not (T). Garland-type cohomology vanishing for unitary coefficients, as used for
  Frobenius-norm stability by de Chiffre--Glebsky--Lubotzky--Thom, needs `H^2` vanishing,
  which `b_2(H) >= 1380` forbids for the trivial representation. So that method cannot
  apply verbatim, and a normalized-HS stability proof must tolerate a large `H^2`.
- **Not attempted yet:** a local spectral (Garland or de la Salle type) stability estimate
  on the links of `Y`, restricted to asymptotic representations that are nontrivial on
  the edge groups.
