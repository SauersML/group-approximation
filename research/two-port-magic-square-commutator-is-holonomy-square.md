---
rg: 2
id: two-port-magic-square-commutator-is-holonomy-square
kind: claim
title: A transverse two-port Magic Square extends exactly the commuting pairs
artifacts:
  - research/two-port-magic-square-holonomy-proof.md
distinct_from:
  magic-square-one-port-is-a-universal-phase-absorber: that proves one port is completely transparent; two transverse ports in one square instead force an exact commutativity quotient.
  row-glued-magic-squares-absorb-noncommuting-ports: that gives a connected multiport absorber when separate cycles have an alignable common row; one irreducible square cannot absorb a noncommuting transverse pair.
  finite-k-commuting-face-universal-completion: that seeks a noncentral packet-to-code coupling; this closes the minimal two-port single-square candidate in both directions.
---

Let `x_(ij)` be nine involutions, commuting within every row and column.
Write `R_i=product_j x_(ij)` and
`C_j=product_i x_(ij)`.  Put source involution ports on one transverse pair
of lines and make the other four line products scalar:

```text
R_1=Z,       C_1=W,
R_2=alpha_2, R_3=alpha_3,
C_2=beta_2,  C_3=beta_3.                               (TP1)
```

Then a perfect representation of this cell exists only if

```text
[Z,W]=1.                                                (TP2)
```

This is not a class-two or Pauli-sector artifact.  Put
`a=x_11,b=x_12,c=x_21,d=x_22,g=x_31` and
`kappa=alpha_2 alpha_3 beta_2 beta_3`.  Exact elimination of the other
four cells gives

```text
x_13=kappa c b g,
(c b g)=(g b c),
[b,c b g]=1.
```

The last two identities imply `(bc)^4=1`, while direct multiplication gives

```text
ZW=kappa (bc)^2.
```

Hence `(ZW)^2=1`, which is equivalent to `ZW=WZ` for involutions.

The condition is also sufficient.  If `Z` and `W` commute, split their joint
spectrum into the four projections `P_(z,w)`.  On the
`(z,w)` sector the six desired scalar line signs have total parity
`z w kappa`.  An even profile has a scalar square; an odd profile has a
two-qubit Mermin--Peres square, and cell-sign gauges reach every profile of
the same total parity.  Taking the controlled direct sum of these
four-dimensional models extends the given pair on `H tensor C^4`.
Therefore the exact port image of the transverse cell is **precisely** the
commuting involution pairs.

The row/column ordering holonomy

```text
Omega=(C_1 C_2 C_3)^(-1)(R_1 R_2 R_3)
```

still records the mechanism: `Omega=kappa WZ=(bc)^2` and
`Omega^2=[W,Z]=1`.  There is no noncentral holonomy escape inside one square.

A dimension-free robust form holds when cell involutions and within-line
commutations are exact.  If the six equations in `(TP1)` have normalized
Hilbert--Schmidt defects `eta_(R_i),eta_(C_j)`, then

```text
||[Z,W]-I||_2
 <= 16 (sum_i eta_(R_i) + sum_j eta_(C_j)).             (TP3)
```

Thus the minimal transverse two-port square is a robust commutativity test,
not a transparent absorber and not a finite-versus-commuting decoder.  A
surviving cyclic coupling needs a larger incidence pattern whose perfect
commuting source sector satisfies its induced port relations while the
finite-dimensional escape cannot.
