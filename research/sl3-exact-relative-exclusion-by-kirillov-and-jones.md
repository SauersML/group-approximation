---
rg: 2
id: sl3-exact-relative-exclusion-by-kirillov-and-jones
kind: route
title: Positive orbit measures remove every primary factor before the coprime Jones contradiction
target: sl3-prescribed-exact-relative-witnesses-do-not-exist
requires:
  - sl3-primary-exact-congruence-mass-vanishes-at-every-prime
  - kazhdan-generator-containment-is-uniform-on-the-group
  - odd-congruence-lambda-exact-sector-collapses
artifacts:
  - research/artifacts/sl3-primary-exact-sector-kirillov-tightness-2026-09-08.md
  - research/artifacts/independent-kirillov-primary-sector-audit-2026-09-08.md
  - research/artifacts/kazhdan-jones-uniform-carrier-containment-2026-09-08.md
---

Use the witness notation of the target. Because pi is a homomorphism
and sigma_n represents its restriction to C, H_n=U_n(h) and sigma_n
satisfy the overlap relations on a fixed Kazhdan set of
D=C intersect h^-1 C h, with errors tending to zero.

The primary artifact proves, for every prime including two, that
sigma_n has genuine coprime representatives beta_n with

    sup_(c in C)||sigma_n(c)-beta_n(c)||_2 ->_omega 0.       (E1)

Its exactness-sensitive steps are: Kazhdan projection produces an
exact intertwiner with polar supports of trace 1-o(1); simultaneous
CRT at precision p^(a_n+2) separates the primary factor; positive
character measures on two fixed uniform pro-p groups share mass
1-o(1); after fattening, any escaping mass would induce a
K- and h-invariant probability on the projective coadjoint space.
That invariant probability cannot exist. Tightness gives uniform
continuity on deep congruence subgroups; h contracts a root into
those subgroups and forces the whole primary factor to be trivial
in normalized 2-norm. Finite tracial coordinates use positive trace
weights and polar support traces in place of integer multiplicities.

For clarity the remaining coprime step also holds in these general
coordinates. Let V'_n=beta_n(h mod m_n), and write
V=[U_n(h)], V'=[V'_n]. The group D surjects onto each coprime
SL_3(Z/m_n), so its exact coordinate commutant is the same as C's.
Their adjoint Kazhdan estimates identify both ultraproduct relative
commutants with the ultraproduct of these coordinate commutants.
As V and V' implement the same conjugation on D,
W=V'^*V belongs to that common commutant. It commutes with every
constant C-unitary and every varying coprime congruence slot.

Let w_12,w_23 be signed permutation matrices in C, and put
h'=w_12 h w_12^-1, h''=w_23 h w_23^-1. The diagonal identity
h h''^-1=h' holds in A and modulo m_n. Writing V=V'W in this
identity gives the slot for h' on its left side and the slot for
h' multiplied by W on its right side. Thus W=1, and

    ||U_n(h)-beta_n(h mod m_n)||_2 ->_omega 0.             (E2)

This is precisely the coprime slot proof; it uses no assertion that
a varying slot belongs to the algebra of constant lattice sequences.

Choose c_n in C reducing to h modulo m_n. By (E1), beta_n has
fixed generators asymptotically contained in B_n. Uniform
Kazhdan--Jones containment gives

    dist_2(beta_n(c_n),B_n)
      <= (2/kappa_C) max_(s in S_C)dist_2(beta_n(s),B_n)
      ->_omega 0.

Together with (E2), this yields dist_2(U_n(h),B_n) ->_omega 0,
so its expectation norm tends to one. The defining outside
expectation for h gives the contradiction.

The proof uses genuine finite congruence lattice representatives
at its first, primary, commutant, and Jones steps. No part supplies
these representatives for an arbitrary scalar relative witness.
