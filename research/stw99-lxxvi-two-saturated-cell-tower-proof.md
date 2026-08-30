---
rg: 2
id: stw99-lxxvi-two-saturated-cell-tower-proof
kind: route
title: Inject the cell cokernel into pi5 and use the order of the scalar class
target: stw99-lxxvi-two-saturated-cell-towers-kill-s6
requires:
  - stw99-lxxvi-higher-nccw-s6-obstruction
artifacts:
  - research/artifacts/stw99-lxxvi-fourth-depth-audit-2026-08-30.md
---

At stage `j`, the cell-fibration exact sequence contains

```text
pi_6(U(M_2(A_(j-1)))) --partial_j-->
pi_(5+k_j)(U(M_2(F_j))) --q_j-->
pi_5(U(M_2(A_j))) -> pi_5(U(M_2(A_(j-1)))).           (4)
```

Suppose inductively that the scalar class vanishes at stage `j-1`.
Exactness puts its stage-`j` image in `image(q_j)`.  Factoring `q_j` through
the cokernel of `partial_j` gives an injection

```text
qbar_j:coker(partial_j) -> pi_5(U(M_2(A_j))).          (5)
```

The unique obstruction coset `omega_j` maps to the scalar class.  Since the
source scalar class has order two,

```text
qbar_j(2 omega_j)=2 alpha_(A_j)=0.
```

Injectivity in `(5)` gives `2 omega_j=0`.  Condition `(3)` is equivalent to
the cokernel having no nonzero element killed by two, so `omega_j=0` and the
scalar class remains zero.  The zero-skeleton class vanishes because each
amplification `U(2)->U(2r_i)`, `r_i>=2`, maps the torsion class into the
torsion-free stable group `pi_5(U)=Z`.  Finite induction proves the theorem.

If one stable cell is attached directly to `A_0`, then
`pi_6(U(M_2(A_0)))=0`.  For odd `k`, Bott periodicity makes the target of
`partial_1` zero; for even `k`, it makes that target free abelian.  In either
case its cokernel has no two-torsion, proving the parity-free one-cell
corollary.  For a stable even cell later in a tower, the target remains a
free lattice, and `(3)` is precisely 2-saturation of the image sublattice.
The degree-six exact sequence also shows that a stable even cell preserves
`pi_6=0`, because its fibre term there is
`pi_(6+k)(U(M_2(F)))=0`.  Consequently the earlier stage needed to feed a
nonzero boundary into a stable even-cell obstruction must itself include an
odd-dimensional cell.

It follows that if all stable even cells precede all stable odd cells, the
even segment preserves both `alpha=0` and `pi_6=0`, while every obstruction
target in the odd segment is zero.  This proves the attaching-map-independent
ordered-tower corollary.
