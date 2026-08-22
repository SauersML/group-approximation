---
rg: 2
id: leavitt-crossed-gram-pauli-charge-has-sectorwise-escape
kind: claim
title: The depth-one crossed-Gram Pauli charge has an exact sectorwise Clifford escape
distinct_from:
  controlled-pauli-commutator-is-and-times-multiplicity-commutator: that gives the abstract controlled-AND commutator and one global multiplicity residue; this instantiates the two Leavitt child ranges and constructs a four-selector-sector exact escape.
  tensor-independent-child-carrier-gap: that pays when one fixed carrier is recovered near both independent child algebras; this shows the crossed Steinberg commutator alone does not recover that carrier.
  first-leavitt-weyl-cell-has-exact-rectangular-model: that gives the two tensor-factor Weyl branch model; this adds the strongest fixed Pauli commutator intended to detect its range overlap.
---

# The depth-one crossed-Gram Pauli charge has an exact sectorwise Clifford escape

ESTABLISHED.  Let `F_0,F_1` be commuting projections and let `X,Z` be a
Pauli pair, commuting with them, with

```text
XZX^(-1)Z^(-1)=-I.
```

Define the controlled gates

```text
A=(1-F_0)+F_0 X,
B=(1-F_1)+F_1 Z.                                      (LPG1)
```

The four selector sectors give the exact identity

```text
[A,B]=1-2F_0F_1,
||[A,B]-1||_2^2=4 tau(F_0F_1).                        (LPG2)
```

Thus one fixed Pauli commutator would indeed turn the Leavitt crossed Gram
`y_0x_1=0` into a dimension-independent overlap payment **if** `(LPG1)` were
authenticated as literal controlled operators.  It preserves exact Leavitt
completeness because the native sibling ranges are orthogonal.

This payment survives a genuinely common irreducible packet and its global
multiplicity twists.  If on one packet type

```text
A=C_A tensor R,          B=C_B tensor T,
[C_A,C_B]=1-2F,          alpha=tau(F)<=1/2,             (LPG2a)
```

then, with `K=[R,T]`,

```text
||[A,B]-1||_2^2
 =2-2(1-2alpha) Re tau(K)
 >=4alpha.                                                (LPG2b)
```

Thus one global gauge cannot cancel the overlap phase without paying at
least the original overlap energy.  A common irreducible Pauli packet would
be a valid one-cell solution.

The native Steinberg zero relation does not authenticate `(LPG1)`.  It only
says that two root words commute.  A finite controlled-Clifford packet also
does not suffice, because its implementers retain multiplicity unitaries.
There is an explicit finite exact escape.

Take four equal selector sectors `H_(ab)`, `a,b in {0,1}`, let `F_0=a` and
`F_1=b`, and on each sector use a label qubit and a gauge qubit.  Define

```text
A_(ab)= I                              if a=0,
        X_label                        if (a,b)=(1,0),
        X_label tensor X_gauge         if (a,b)=(1,1),

B_(ab)= I                              if b=0,
        Z_label                        if (a,b)=(0,1),
        Z_label tensor Z_gauge         if (a,b)=(1,1).   (LPG3)
```

On the overlap sector, the label commutator and gauge commutator are both
`-I` and cancel.  On each other sector at least one gate is the identity.
Consequently

```text
[A,B]=1,                 tau(F_0F_1)=1/4.              (LPG4)
```

All operators are involutions.  The gauge factors commute with the local
label operators, so they do not alter any **sector-preserving**
conjugation/covariance relation used by separate typed child packets.  If zero trace is required for
the two return words, multiply `A` by the second selector sign and `B` by
the first; these central signs cancel the two inactive-sector traces and do
not change their commutator.  Passing to the regular representation of the
finite generated matrix group preserves all exact relations and gives every
selector sector positive Plancherel mass.

This model deliberately fails an additional packet flip which connects the
four selector sectors and makes their sum one irreducible type: Schur's
lemma would then force one global pair `R,T`, and `(LPG2b)` would apply.
Exactly such a connector is absent from the native crossed Steinberg zero
relation and from the typed rectangular branch returns.  Adding it is the
common-packet/same-reservoir authentication being sought.

The same escape is already visible in the rectangular Weyl model: the two
child algebras are tensor factors, their standard half-carriers have overlap
`1/4`, and unconditioned cross-root words commute exactly.  Formula `(LPG2)`
detects the overlap only after replacing those root words by support-
controlled gates; `(LPG3)` shows that finite Clifford covariance does not
make that replacement representation-independent.

Hence the one-cell analytic inequality exists, and even arbitrary **global**
multiplicity holonomy cannot defeat it.  It does not prove the paired
same-reservoir lemma from the current Steinberg relations because those
relations allow the holonomy to vary by typed selector sector as in
`(LPG3)`.  The exact remaining input is one bounded relation connecting the
four selector sectors into a common irreducible packet, or an independent
charge for that sectorwise gauge variation.  This is the same-reservoir
problem in its smallest depth-one form.
