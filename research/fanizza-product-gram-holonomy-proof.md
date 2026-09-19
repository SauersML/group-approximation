---
rg: 2
id: fanizza-product-gram-holonomy-proof
kind: route
title: Pull context PVMs to one root and telescope every consistency row
target: fanizza-product-gram-reduces-to-one-state-holonomy
requires: []
---

Choose a spanning tree and define rooted transports `V_r=I`,
`V_d=U_eV_c`.  Pull back each context observable by
`A-hat_(c,x)=V_c^*A_(c,x)V_c`.  For an anchor context `a(x)` and an
`x`-labelled path transporter `W_(c,x)`, set

```text
H_(c,x)=V_c^*W_(c,x)V_(a(x)).
```

Pathwise covariance telescoping gives

```text
||(A-hat_(c,x)H-H A-hat_(a(x),x))G||_2
 <= path edge error.
```

Adding and subtracting `H` and using the anchor row yields

```text
||A-hat_(c,x)G-GB_x||_2
 <=2||(H-I)G||_2+path error
   +||A-hat_(a(x),x)G-GB_x||_2.
```

Forbidden-answer norms are unchanged by the rooted transport.  Squaring and
summing the fixed incidence list proves the full game-energy bound.

For the native graph, a tree contains the leaf and two triangle edges, so
only the chord contributes holonomy.  Its word is
`U_DR^(-1)U_ZR U_DZ`.  Ordinary edge relations cannot control it: amplify
all vertex packets by one multiplicity space, take identity multiplicity
actions on tree edges and `-I` on the chord.  Every local relator remains
exact while `||(H-I)G||_2^2=4||G||_2^2`.  The single two-cell
`U_ZR U_DZ=U_DR` kills this term identically.  The derivation uses no claim
about Gram mass or local acceptance, so those remain separate rows.
