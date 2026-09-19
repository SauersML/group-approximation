---
rg: 2
id: six-generator-one-jump-router-has-s3-radical-atlas
kind: claim
title: A six-generator one-rank-jump packet has a transitive three-chart radical atlas
artifacts:
  - experiments/two_flag_mixed_router_search.py
distinct_from:
  mixed-central-cnot-completes-relative-rank-one-router: that is the minimal four-generator one-shear packet; this adds one base pair and obtains three genuinely distinct endpoint charts.
  robust-rank-one-endpoint-marginal-floor: that is an abstract measure inequality once three charts share marginals; this constructs a finite class-two packet with the required three-chart symmetry.
---

Let `K,J` be central involutions and let the six noncentral involutions be

```text
x_0,z_0,x_1,z_1,x_2,z_2.                              (SRA1)
```

All commutators are central.  In additive form, the `J` commutator form has
an edge between every pair in `(SRA1)` except two distinct `z` generators.
The `K` form has exactly the edges

```text
[x_i,x_j]=K                 (i!=j),
[x_i,z_j]=K                 (i!=j),                    (SRA2)
```

and no others.  Equivalently, in the pair order

```text
01,02,03,04,05,12,13,14,15,23,24,25,34,35,45,
```

the forms are

```text
J=(1,1,1,1,1,1,0,1,0,1,1,1,1,0,1),
K=(0,1,1,1,1,1,0,1,0,0,1,1,1,0,0).                  (SRA3)
```

Their central-character alternating ranks are

```text
(K,J)=00:0,       01:4,       10:4,       11:6.       (SRA4)
```

Thus on the marked `J=-1` sector, switching `K` from `+1` to `-1`
adds exactly one Pauli qubit.

Every permutation of the three ordered pairs `(x_i,z_i)` preserves both
quadratic forms, not merely their alternating polarizations.  It therefore
gives an honest automorphism of the finite class-two packet.  On the allowed
`K=+1,J=-1` sector, the `J` form has radical

```text
R_z={000,011,101,110} subset span{z_0,z_1,z_2}.        (SRA5)
```

The `S_3` automorphisms act transitively on the three nonzero radical signs

```text
z_1z_2,             z_0z_2,             z_0z_1.       (SRA6)
```

These are three literal, commuting endpoint words carried by one fixed
finite packet.  Unlike the four-generator router, the relative radical
endpoint is not fixed by the automorphism group.

The exhaustive verifier checks all `2^15` quadratic forms and all `168`
linear actions on the three-dimensional endpoint plane.  It also proves a
useful minimal-ansatz obstruction: two prescribed independent CNOT shears
admit invariant marked forms only of ranks `0,2,6`, never rank four.  The
transitive atlas above has stabilizer order six; its marked form has the
smallest weight found in that class.

This is an algebraic atlas, not yet the active-return payment theorem.  The
next step must couple the three radical endpoint words to the three
rank-one contexts while retaining all four allowed radical characters.
