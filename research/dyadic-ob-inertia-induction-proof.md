---
rg: 2
id: dyadic-ob-inertia-induction-proof
kind: route
title: Pull back the beta-one edge block and induce from the opposite inertia group
target: dyadic-ob-inertia-arrows-have-exact-induction-functors
requires:
  - adjacent-clifford-orbit-transition-graph
  - adjacent-clifford-flow-has-one-third-rank-deficit
  - fixed-clifford-projective-dyadic-tower
---

Write an abstract upper-Iwahori element as

```text
gamma=[[x,y],[z,w]],                 z even,
sigma(gamma)=[[x,2y],[z/2,w]].                         (DOP1)
```

If `sigma(gamma)=1 mod 2^(a+1)`, then

```text
x,w=1 mod 2^(a+1),  y=0 mod 2^a,  z=0 mod 2^(a+2),
```

so `gamma=1 mod 2^a`.  Hence `(DOP1)` induces the well-defined surjection
`r_a` in `(DOI1)`.  Modulo two, `B_(a+1)^-` is the lower Borel of
`SL_2(F_2)`.  It fixes the newest-layer character

```text
ell_B(A,B,C)=B=(0,1,0),                                (DOP2)
```

and has index three.  It is therefore exactly the inertia group of
`ell_B`, not merely a subgroup of it.

The upper Borel permutes newest-layer dual characters while preserving the
condition `beta=1`; consequently `W_1(V)` is `B_a^+`-invariant.  For

```text
h=1+2^a X(A,B,C) in L_(a+1),
```

the pullback calculation gives

```text
r_a(h)=1+2^(a-1)X(0,B,0) in L_a.                       (DOP3)
```

Every character in `W_1(V)` evaluates `(DOP3)` as `(-1)^B`.  Thus
`L_(a+1)` acts on `W_1(V) o r_a` by `ell_B`.  Clifford induction from its
full inertia group proves that `(DOI2)` is an ordinary `G_(a+1)`-
representation lying over `O_B`.  This ordinary construction also proves
factor-set compatibility: the OB inertia multiplier is precisely the one
linearized by the pulled-back edge module, so no independent projective
sign can obstruct the arrow.

In the restriction of the induced representation back to
`B_(a+1)^-`, the functions supported on the identity coset form a copy of
the inducing module.  Under `r_a` this copy is exactly `W_1(V)`, so `(DOI2)`
constructs the asserted edge intertwiner rather than only a vertex
representation with the right orbit.

If `V` lies over `O_F={(1,1,1)}`, all of `V` has `beta=1`.  If it lies over

```text
O_B={(0,1,0),(0,1,1),(0,0,1)},
```

Clifford theory gives the three character spaces equal dimension and
exactly two have `beta=1`.  Therefore `W_1(V)` has the two dimensions in
`(DOI3)`.  Since the inertia index is three, induction multiplies each by
three, proving all of `(DOI3)`.

For the recurrent `O_B` arrow, the edge module has dimension `2 dim(V)/3`
while the induced target has dimension `2 dim(V)`; it occupies one target
Clifford character block.  Hence iteration retains the fraction `2/3` of
the preceding source at each step but triples that retained module to form
the next vertex packet.  A fixed-orbit summand obeys the same universal
target-to-edge ratio three.  Therefore mixing arbitrary multiplicities of
the two functors cannot enlarge the unique target character slot.  Summing
over targets recovers the one-third bound in
`adjacent-clifford-flow-has-one-third-rank-deficit`; applying the transposed
bound to the other orientation gives total adjacent common mass at most
two thirds.

Conjugating by the Weyl element (equivalently transposing the root charts)
repeats the proof with `gamma=1`.  The orbit `O_B` again has exactly two of
three such characters, so both dimension factors are unchanged in the
reverse adjacent orientation.
