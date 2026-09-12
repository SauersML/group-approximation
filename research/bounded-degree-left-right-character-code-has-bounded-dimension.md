---
rg: 2
id: bounded-degree-left-right-character-code-has-bounded-dimension
kind: claim
title: A bounded-degree left-right vertex-square code cannot be the growing simplex code
distinct_from:
  signed-character-expansion-decodes-operator-parallelograms: that proves operator soundness for this code under a signed gap; this proves its classical dimension is too small for the required metapixel.
---

ESTABLISHED.  On a left-right Cayley square complex
`Cay2(A,G,B)`, put one bit `f(g)` on each vertex and impose even parity on
every square `{g,ag,gb,agb}`.  If both `A` and `B` generate `G`, the exact
code is

```text
f(g)=c+chi(g),     c in F_2, chi in Hom(G,F_2).             (LRC1)
```

Consequently

```text
dim C = 1+dim Hom(G,F_2) <= 1+min{|A|,|B|}.                 (LRC2)
```

Thus no family with bounded left and right degrees can realize affine
simplex codes of dimensions tending to infinity by putting the distinguished
bits directly on the vertices and using only the bare square parity checks.
This remains true even when the complex has excellent ordinary, signed, or
high-dimensional expansion.

The left-right construction can still be an operator-sound constant-size
building block by
`signed-character-expansion-decodes-operator-parallelograms`, but a growing
simplex metapixel must add auxiliary proof coordinates and a tensor/PCPP
layer.  The published left-right Cayley LTCs do exactly use bits on squares
and nontrivial base tensor codes; their classical theorem does not supply the
same-Hilbert operator decoder required here.
