---
rg: 2
id: tree-face-separator-signedness-is-removable-modulo-the-unit
kind: claim
title: The essential tree-face separator has a positive Choi representative modulo unit evaluation
distinct_from:
  three-face-quotient-separators-are-not-one-face-local: that produces a quantitatively essential bounded tree-face component of a quotient separator; this converts that signed component to a positive Choi/GNS witness on every unital-zero defect.
  finite-packet-triangle-repair-is-ideal-block-choi-feasibility: that gives arbitrary signed finite-packet separation functionals annihilating a prescribed reservoir; this is a finite-face order-duality lemma at the quotient level and does not make packet representations or ideal supports uniform.
  exhausting-ideal-reservoirs-have-lift-or-quotient-separator: that explains when varying packet certificates have a bounded quotient-level limit; this starts with such a bounded limit and removes signedness from one finite tree-face component without producing a finite-dimensional representation of the quotient.
---

**ESTABLISHED (positive Choi conversion).**  Let `B` be a finite-dimensional
unital C-star algebra, let `Q` be any unital C-star algebra, and let `F` be a
bounded Hermitian functional on the self-adjoint map space
`L_sa(B,Q)`.  There is a bounded Hermitian functional `F_pos` on the same map
space such that

```text
F_pos(theta)>=0                    for every cp theta:B->Q,       (PCU1)
F_pos(psi)=F(psi)                  whenever psi(1_B)=0.           (PCU2)
```

Thus every signed functional on differences of unital maps has a positive
Choi representative.  The conversion is quantitative with a constant
depending only on the finite algebra `B`: under any fixed Choi
identification,

```text
||F_pos|| <= C_B ||F||.                                        (PCU3)
```

Apply this to the component decomposition in
`three-face-quotient-separators-are-not-one-face-local`.  If `ell` has
separator gap `delta`, at least one tree face `H in {P_12,P_23}` has a
component `ell_H` satisfying

```text
ell_H((id-M_(P_13))|_(C^*(H))) >= delta/2.                    (PCU4)
```

The displayed defect sends the unit to zero.  Hence `ell_H` has a positive
Choi representative `ell_H^pos` with exactly the same value in `(PCU4)`.
If the separator is normalized and the fixed face splitting is fixed, then
after normalizing `ell_H^pos` one obtains a positive Choi state whose value
on that tree defect is at least

```text
c_H delta>0                                                       (PCU5)
```

for a constant `c_H` depending only on the finite face and the chosen fixed
splitting, never on a representation packet or reservoir depth.

Equivalently, the essential tree term can be represented by a vector in the
GNS representation of the finite Choi algebra

```text
direct_sum_r M_(n_r)(Q),       C^*(H)=direct_sum_r M_(n_r).       (PCU6)
```

**Sharp scope.**  This removes *order signedness*; it does not make the GNS
representation finite-dimensional, normal with respect to a prescribed
trace, or supported in any fixed relator reservoir.  Consequently it does
not turn `(PCU5)` into a low-relator-spectrum finite matrix witness.  The
remaining obstruction is representation/support control, not positivity of
the finite tree-face Choi functional.

Proof: `dominate-the-negative-choi-part-by-its-unit-marginal`.

DERIVATION
dominate-the-negative-choi-part-by-its-unit-marginal
