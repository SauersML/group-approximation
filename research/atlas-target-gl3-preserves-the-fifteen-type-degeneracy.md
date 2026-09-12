---
rg: 2
id: atlas-target-gl3-preserves-the-fifteen-type-degeneracy
kind: claim
title: The shortest target-mixing Atlas rows preserve all fifteen degenerate CK types
distinct_from:
  atlas-three-transverse-shears-leave-fifteen-character-types: that classifies the three source-to-target shears and counts their exceptional target characters; this adds the first rows mixing the three target directions and computes their action on those exceptional types.
  atlas-a4-19243-parabolic-subgroup-ladder: that identifies a GL3(2) subgroup inside the finite A8 collision ladder; this is the rank-five Steinberg target-star action on CK p/q characters and its orientation invariant.
  atlas-pauli-branch-recurrence-automaton: that asks for a low-energy recurrent coefficient automaton; this proves the entire coefficient-one target-basis automaton preserves the bad orientation classes.
---

**ESTABLISHED EXACT NO-GO FOR THE SHORTEST NON-SOURCE-SHEAR ROWS.**  For
distinct `r,s in {3,4,5}`, put

```text
R_rs=x_rs(1),       D_(r,a)=x_1r(a).                  (TGL1)
```

The shortest literal rows which mix two target directions are

```text
[D_(r,a),R_rs]=D_(s,a).                               (TGL2)
```

Thus conjugation by `R_rs` performs the elementary basis change

```text
D_(r,a) |-> D_(r,a) D_(s,a),                         (TGL3)
```

fixing the other target directions.  The coefficient-one roots `R_rs`, in
both orientations and for all pairs, generate `GL_3(F_2)` on the three
target positions.  They simultaneously apply the same basis change to the
`p`, `q`, and `1=p+q` sign vectors

```text
(u,v,w) |-> (g u,g v,g w),       w=u+v,              (TGL4)
```

up to the harmless transpose convention for character coordinates.

The three-shear degeneracy condition

```text
u in span_F2{w}                                       (TGL5)
```

is invariant under every `g in GL_3(F_2)`.  More precisely, the fifteen
degenerate target types split into three `GL_3(F_2)`-invariant strata:

```text
A: (u,w)=(0,0),                         size 1,
B: u=0, w!=0,                           size 7,
C: u=w!=0,                              size 7.        (TGL6)
```

`GL_3(F_2)` is transitive on each of `B` and `C`, but no target basis change
interchanges the three strata.

These target-mixing rows also do not couple the two marked CK orientations.
Every `R_rs` commutes with the source roots `x_12(p),x_12(q)`.  Combining
all target basis changes with all three source shears therefore still leaves,
inside each stratum in `(TGL6)`, two distinct marked affine orbits: one in
which the `p` cut is selected and one in which the `q` cut is selected.  No
word in the resulting semidirect product pairs them.

The canonical masses remain

```text
stratum A: 1/64,       stratum B: 7/64,
stratum C: 7/64                                         (TGL7)
```

in the target-character profile, and half those values after intersecting
with the marked source sign.  Hence adjoining the complete coefficient-one
`GL_3(F_2)` target packet does not shrink the `15/64` degeneracy face at all.

Exact finite-dimensional survivor models are obtained from the permutation
representations of any one of the six marked orientation orbits in
`A,B,C`.  The corresponding orbit projection commutes with the whole finite
source-shear/target-basis packet, so external multiplicity may be placed on
one orientation without the other.

Therefore the first genuine target-mixing rows do not close the Atlas face.
Any useful next row must use a nontrivial coefficient on the moving target
root, or a different root incidence which acts nonlinearly on `(u,w)`; pure
coefficient-one basis changes are exhausted by `(TGL4)`.

DERIVATION
atlas-target-gl3-degeneracy-proof
