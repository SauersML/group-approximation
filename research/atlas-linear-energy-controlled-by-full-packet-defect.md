---
rg: 2
id: atlas-linear-energy-controlled-by-full-packet-defect
kind: claim
title: The linearized atlas energy is bounded by the full packet defect including the interior separator
distinct_from:
  atlas-fold-localization-with-uniform-remainder: that asks for a metric localization of low-defect microstates near the classical fold; this asks for one inequality between two explicit energies, with no neighbourhood, no gauge and no remainder in the statement. It is what that localization was wanted FOR, and it is checkable at every finite multiplicity.
  atlas-boundary-tangent-covariance-coercivity: that is the ESTABLISHED half -- the covariance energy is at most 1/14 of the linearized energy, for every matrix at every multiplicity; this is the missing half, comparing the linearized energy to the true defect.
artifacts:
  - research/artifacts/atlas-asc-tangent-exact-2026-08-19.md
  - experiments/atlas_asc_link_probe.py
  - experiments/atlas_asc_inner_link_scan.py
---

OPEN.  For a unitary `U in U(20160k)` and a fold-trivial atlas word `s`, put

```text
l_s = ||rho(z_s) U||_2,     z_s = sum_j (u_j - v_j) in Z[A_8],
```

the linearized energy of `atlas-boundary-tangent-covariance-coercivity`, and
write `S_0` for the 234 first-boundary words together with the interior
separator `c_19243`.  Ask for a constant `C'`, independent of `k`, with

```text
sum_(s in boundary) l_s^2
   <=  C' * sum_(s in S_0) ||pi_U(s)-1||_2^2.                       (LINK+)
```

**Why the interior word must be on the right.**  Without it the statement is
false, and provably so.  The exact characteristic-two countermodel of
`ATLAS_BOUNDARY_RANK_THREE_EXACT_AUDIT` -- `E = M semidirect A_8`,
`dim_F2 M = 155`, both chart restrictions regular, hence conjugate by some
unitary at multiplicity `|M|` -- makes every boundary defect exactly zero
while the two `H` copies still disagree, so `a^2+b^2 > 0` there.  Since
`a^2+b^2 <= (1/14) sum_s l_s^2` holds for every matrix, the left side of
(LINK+) is strictly positive while a boundary-only right side is zero.  The
same countermodel is killed by the interior centrality condition attached to
collision word 19243, which is why `S_0` is the packet that can work.

**What is known in its favour.**  Measured on the exact model at `k = 1`
(`experiments/atlas_asc_link_probe.py`): the ratio of the two sides is
`1.00002` at normalized distance `0.03` from the classical fold, `1.05` at
`0.3`, and only `3.24` at a Haar-random chart unitary -- the linearized and
true energies track each other closely over the whole accessible range.  And
the inner case is decided exactly rather than numerically
(`experiments/atlas_asc_inner_link_scan.py`): of all 20160 inner chart
conjugators exactly one kills all 234 boundary words, the identity, and there
every `l_s` vanishes -- so no inner counterexample exists and every
counterexample must be non-inner, as the characteristic-two one is.

**What it buys.**  With the established global bound it gives
`a^2+b^2 <= (C'/14) sum_(s in S_0) ||pi_U(s)-1||_2^2` outright, hence (ASC),
hence a non-hyperlinear group: see
`nonhyperlinear-from-linear-energy-domination`.

**A bridge to the existing machinery.**  `z_s` is the integral lift of the
audit's characteristic-two derivative `d_q = sum_j (p_(j-1) + p_j)`: same
signed prefix sums, reduced mod 2.  So the object whose mod-2 cokernel
carries the countermodel (`M = F_2[A_8]/I`, dimension 155) and the object
whose complex kernel gives the constant 1/14 (dimension 120 = [A_8 : GL_3(2)])
are the same 234 elements in two characteristics.  A proof of (LINK+) may
well be the statement that the interior separator closes the mod-2 hole that
the complex inequality is missing.

**Why it is not a Taylor estimate.**  `pi_U(s)-1 = sum_j (W_j-1) + cross`,
and in normalized Hilbert--Schmidt the cross terms are not second order:
`||(A-1)(B-1)||_2` only yields `||A-1||_op ||B-1||_2`.  That is exactly the
operator-norm-versus-HS gap that separates MF from hyperlinear, so a proof
has to use the atlas relations and not merely the size of the defects.
