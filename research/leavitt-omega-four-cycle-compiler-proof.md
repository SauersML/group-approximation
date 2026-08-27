---
rg: 2
id: leavitt-omega-four-cycle-compiler-proof
kind: route
title: Identify the carrier corners through the source identity and expose the target
target: leavitt-omega-four-cycle-compiler
requires:
  - leavitt-omega-has-an-explicit-distorted-target
  - leavitt-two-relator-corner-peeling
---

The explicit Leavitt calculation gives

```text
S=Omega(a,r)=1,                 T=Omega(c,p)=h!=1.
```

The first relator of `P` is therefore `YH^(-1)=1`, hence `Y=H`.  Substitution
in the second relator gives

```text
H h H^(-1)=1,
```

and conjugating by `H^(-1)` gives `h=1`.

Each of `H,Y` has total incidence degree two in the two relators.  The
incidence graph is the four-cycle with the two relator vertices on one side
and the two long-corner vertices on the other.  In particular it has nonempty
two-core and evades the reversible singleton eliminations which fenced the
degree-four and affine-Omega candidates.

To obtain a nonsingular one-relator KL word, add a unary cyclic-cover orbit
`Hz=1`.  It supplies the nonzero-degree pivot `z=H^(-1)`; the two displayed
relations are then the required other orbit relators after substitution.
This last sentence is a realization specification, not a claim that a cyclic
word realizing the incidence has already been found.
