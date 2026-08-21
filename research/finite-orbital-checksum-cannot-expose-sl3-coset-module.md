---
rg: 2
id: finite-orbital-checksum-cannot-expose-sl3-coset-module
kind: claim
title: Finitely many orbital lamp checks cannot algebraically expose the full SL3 coset module
distinct_from:
  finite-presentation-must-expose-whole-module-with-uniform-defect: that asks for a matrix-only uniform exposure theorem; this proves that no ordinary algebraic consequence of finitely many prototype lamp relations can supply it.
  arithmetic-global-pvm-does-not-bypass-coset-action-gate: that identifies the finite atomic enemy after global PVM rounding; this identifies the earlier finite-orbital word obstruction before rounding.
  wreath-presentation-double-coset-obstruction: that gives the general finite-presentation obstruction; this spells out its exact partial-graph-product countermodel for the SL3 checksum proposal.
---

ESTABLISHED.

Let

```text
C=SL_3(Z) < A=SL_3(Z[1/2]),       X=A/C,
```

and let `c_x` be involutory lamps.  A prototype commutator

```text
[c_C, g c_C g^-1]=1                                      (FOC1)
```

and all its actor conjugates impose commutation exactly on the orbital of
ordered pairs indexed by the double coset `C g C`.  Hence finitely many
prototype relations see only finitely many members of `C\A/C`.

The double-coset set is infinite.  Given a finite symmetric collection
`Sigma subset C\A/C`, form the `A`-invariant graph on `X` whose edges are the
orbitals in `Sigma`, and let `K_Sigma` be the graph product of one `C_2` at
each vertex.  Then

```text
P_Sigma=K_Sigma rtimes A                                 (FOC2)
```

is an exact group model of the actor presentation, root involution, root
stabilizer relations, and every selected prototype commutator.  If
`C g C` is outside `Sigma`, the two corresponding vertex generators do not
commute in the graph product.  Thus no van Kampen/ordinary word argument from
the finite prototypes controls that missing lamp pair.

The obstruction also covers an arbitrary finite family of checksum words
which are valid in the full abelian coset lamp group.  The actor is finitely
presented and `C` is finitely generated, so the actor, root involution and
root-stabilizer relations are already finite.  If finitely many additional
valid checksum words implied all conjugate-lamp commutators, they would give
a finite presentation of

```text
(direct_sum_(A/C) C_2) rtimes A.                           (FOC3)
```

The permutational-wreath finite-presentation criterion forbids this because
`C\A/C` is infinite.  Therefore a successful checksum cannot be a purely
algebraic self-similar propagation of finitely many word identities.

This does **not** refute a matrix-only normalized-HS inequality.  Such an
inequality may exploit finite-dimensional co-density and canonical trace
tests, properties absent from `(FOC2)`.  It proves exactly where the needed
new input must enter: a finite-matrix relative-commutant/correctability
theorem, not another conjugacy or first-hit telescope of the prototype lamp
relators.
