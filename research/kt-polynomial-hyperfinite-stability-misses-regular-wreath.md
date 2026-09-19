---
rg: 2
id: kt-polynomial-hyperfinite-stability-misses-regular-wreath
kind: claim
title: The Kun--Thom polynomial base is hyperfinitely HS-stable, but canonical wreath microstates lie outside that class
distinct_from:
  affine-whitehead-hyperfinite-stability-misses-canonical-mark: That treats a noncommutative affine-Leavitt Steinberg quotient; this uses the commutative polynomial elementary group occurring in the Kun--Thom pair and also audits the exact-base-only compressor shortcut.
  character-rigidity-equals-hyperfinite-hs-stability: That is the Dogon--Vigdorovich equivalence for higher-rank lattices; this applies their general character criterion to EL over a polynomial ring and identifies the regular-character firewall.
  kt-single-compressor-canonical-lamps-do-not-exactify-actor: That proves one-compressor actor nonexactification from canonical lamps; this identifies why hyperfinite stability of the exact base does not apply and why exactifying only that base still does not suffice.
---

**ESTABLISHED, SOURCE- AND COUNTERMODEL-AUDITED 2026-08-24.**  Let

```text
R=F_q[x_1,...,x_d],
Gamma=EL_r(R),
r>max{sr(R),2}.                                        (KHF1)
```

Thus one may take `r>=5` for the three-variable Kun--Thom polynomial
stabilizer, since `sr(R)<=dim(R)+1=4`.  Then `Gamma` is hyperfinitely
Hilbert--Schmidt stable in the sense of Dogon--Vigdorovich.

The theorem does **not** exactify the restriction of a canonical wreath
microstate.  The normalized traces of such a restriction converge to the
regular character

```text
delta_e|Gamma.                                          (KHF2)
```

Its GNS algebra is `L(Gamma)`.  The group `Gamma` is infinite and has
property `(T)`, hence is nonamenable; therefore `L(Gamma)` is nonamenable and
nonhyperfinite.  Consequently the restriction in `(KHF2)` is outside the
defining hyperfinite-limit hypothesis of the stability theorem.  Finite
matrix approximants are not automatically a hyperfinite asymptotic
representation: the adjective refers to the marked tracial GNS limit, not
to each finite-dimensional coordinate algebra.

There is also no valid replacement of the missing hypothesis by

```text
"Gamma is represented exactly at each matrix stage."                    (KHF3)
```

Indeed, for any injective endomorphism `alpha:Gamma->Gamma` and any exact
finite-dimensional representation `sigma`, the endomorphism-orbit chain

```text
pi_L(g)=direct_sum_(j=0)^(L-1) sigma(alpha^j(g))         (KHF4)
```

is an exact representation of `Gamma`.  The cyclic block shift `u_L`
satisfies

```text
max_(g in S)||u_L pi_L(g)u_L^*-pi_L(alpha(g))||_2
 <=2/sqrt(L)                                            (KHF5)
```

for every fixed finite generating set `S`.  For the polynomial shear and
finite quotient tower of `one-compressor-covariance-has-free-hs-telescope`,
there are `z_L in pi_L(Gamma)'` and a fixed `gamma in Gamma` with

```text
liminf_L ||[u_L z_L u_L^*,pi_L(gamma)]||_2>=sqrt(2).    (KHF6)
```

Thus exactness of the base and vanishing compressor covariance defect coexist
with macroscopic strict relative-commutant/lamp separation.

Property `(T)` does give the correct but weaker conclusion.  Applying
`kazhdan-polar-rounding-produces-supported-gallery-edges` to `(KHF5)`
produces an exact intertwining partial isometry `b_L` with

```text
tr(1-b_L^*b_L), tr(1-b_Lb_L^*)=O(1/L),
||u_L-b_L||_2=O(1/sqrt(L)).                              (KHF7)
```

In the orbit chain `b_L` is the non-wrapping block shift.  Its source and
range omit different endpoint blocks.  Those moving supports allow the
nested commutants in `(KHF6)` to change on every interior level, so
finite-dimensional commutant no-growth cannot be applied as if `b_L` were a
global unitary intertwiner on one common carrier.  This is a concrete
countermodel to the proposed implication

```text
exact Gamma + approximate one-compressor covariance
  => canonical lamp collapse.                           (KHF8)
```

Only a simultaneous multi-compressor theorem which aligns the polar
source/range supports, or a genuinely nonhyperfinite stability theorem, can
advance this route.

The hyperfinite-stability proof and source pins are in
`kun-thom-hyperfinite-character-firewall-proof`.  The exact-base telescope
and its macroscopic strictness are proved in
`one-compressor-covariance-has-free-hs-telescope` and the corresponding
polynomial-shear quotient-tower theorem recorded in `notes/NOTEPAD.md`.
