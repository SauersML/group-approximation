---
rg: 2
id: native-j1-gl5-source-stabilizer-proof
kind: route
title: Compute the five-projective-summand native actor and its source stabilizers
target: native-j1-extension-gives-gl5-but-only-second-whitehead-gram
requires:
  - endpoint-order-five-actor-has-half-gram
  - native-whitehead-corner-collapses-hecke-flags
---

The coefficient equalities `a_ib_i=q` and `b_ia_i=e_i` identify the five
summands in `(GFI1)`.  The already faithful `GL_4(F_2)` block contains all
coordinate permutations and one elementary transvection on
`<u_0,u_2,u_3,u_4>`.  Adjoining the transposition `J_1=(u_1 u_2)` gives all
five coordinate permutations.  Conjugating the existing transvection by
those permutations gives every elementary transvection, which generates
`GL_5(F_2)`.  The block support also proves identity on `1-D_5`; this proves
`(GFI2)` without enumerating its 9,999,360 elements.

The subgroup `(GFI3)` fixes `u_0,u_1,u_2` as vectors and covectors.  Direct
root support therefore fixes `C_1,C_2,C_3,v,w,s` and their signs.  On the
two remaining row-six roots it is the standard `GL_2(F_2)` action.  Its
character orbits are zero and the three nonzero characters.  The formulas
for `q_2` and `q_1` are `(CNW5)`.  A hyperplane in `F_2^2` contains zero and
one nonzero character, proving `(GFI5)`; `r` is fixed, proving the stated
one-sided fence.  The calculation deliberately stops at `K_2`: replacing
the four additional coefficient roots of the complete source `L_0` by
bare projective incidences is not faithful to their Leavitt coefficients.
