---
rg: 2
id: ghb7-congruence-kernel-flexibly-hs-stable
kind: claim
title: The torsion-free congruence kernel of GHB_2(7) is flexibly Hilbert--Schmidt stable
distinct_from:
  kazhdan-hyperbolic-b2-group-flexibly-hs-stable: that is the existential premise over all hyperbolic Kazhdan groups with b_2 >= 1; this is one explicit instance, the kernel H of the quotient of GHB_2(7) into SL_4(F_7), whose image is Sp_4(F_7)
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
- **Exact invariants (`ghb7-quotient-image-is-sp4-f7`, 2026-09-12).** The image of `ψ` is
  `Sp_4(F_7)`, not `SL_4(F_7)`. So `[G:H] = 276595200`, `χ(H) = 159091200`,
  `b_2(H;Q) = 159091199`, and `b_2^(2)(H) = 159091200`
  (`ghb7-l2-betti-two-is-orbifold-euler-characteristic`).
- **The cohomological existence scheme is blocked (`ghb7-kernel-blocks-degree-two-newton-stability`).**
  - **What stability needs.** It is a degree-two existence statement. Degree one, from
    property (T) or the link spectral gaps of `Y`, gives only rigidity (uniqueness of
    rounding, (T;FD)).
  - **Why the scheme fails for `H`.** Solving `δy = c` for the relator-defect cocycle in
    the `Ad`-module `L²(M)` needs `H^2(H;π) = 0`. For `H` this fails on the trivial summand
    (`b_2 >= 1380`). Whenever `H` is hyperlinear it also fails on a traceless regular
    summand of the `Ad`-module of `σ ⊗ σ`, because `b_2^(2)(H) = χ(H) > 0`.
  - **Consequence.** A local spectral (Garland or de la Salle type) estimate on the links
    of `Y` controls degree one only, and no degree-two vanishing is available on either
    summand. A stability proof for `H` must show that defect cocycles avoid the nonzero
    classes, or use a non-cohomological mechanism.
  - **Artifact:** `research/artifacts/ghb7-kernel-stability-criterion-2026-09-12.md`.
