---
rg: 2
id: hyperfinite-factor-qd-forces-unitary-subgroups-mf
kind: claim
title: If the hyperfinite II1 factor is quasidiagonal then every countable subgroup of U(R) is an MF group
distinct_from:
  stw99-problem-x2-hyperfinite-factor-quasidiagonal: that is the open question whether R is quasidiagonal; this is an unconditional implication from that question to group theory, established here.
  stw10-x2-reduces-to-finitely-generated-weakly-dense-witnesses: that reduces X(2) to finitely generated subalgebras of R; this specialises the subalgebra to a group C*-algebra C*(Γ) for Γ inside U(R) and reads the conclusion as the MF property of Γ.
artifacts:
  - research/artifacts/stw99-x2-unitary-subgroup-reduction-2026-08-30.md
---

Let `R` be the hyperfinite II₁ factor.  If `R` is quasidiagonal as a
C\*-algebra, then every countable subgroup `Γ ≤ U(R)` is an MF group in the
sense of Carrión--Dadarlat--Eckhardt: there are unitaries `V_n(g)` in matrix
algebras with `‖V_n(gh) − V_n(g)V_n(h)‖ → 0` and `limsup ‖V_n(g) − 1‖ > 0`
for `g ≠ 1`.

Consequently a single countable non-MF group inside `U(R)` refutes STW
Problem X(2), and with it Problem X(1) (route `stw99-x1-implies-x2`).

The groups that sit inside `U(R)` are exactly the countable groups with a
faithful character whose GNS closure is hyperfinite
(`τ(g) ≠ 1` for `g ≠ 1`, `π_τ(Γ)''` injective).  Every residually finite group
and every amenable group is such a group, and those are MF anyway; the
content of the implication is on the non-residually-finite,
non-amenable part of `U(R)`.  Kazhdan groups cannot supply a witness:
`kazhdan-groups-in-hyperfinite-unitary-group-are-rf`.
