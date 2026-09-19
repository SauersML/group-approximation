---
rg: 2
id: agent-free-compressor-minimal-corner-proof
kind: route
title: Compare the parent and child Reynolds ranges on the identified stable corner
target: agent-free-compressor-minimal-nonretractive-corner
requires: []
---

Let a finite-dimensional coefficient module act on `H` and set `K=PH`.
Centrality of `P` and `(MNC3)` give on `K`

```text
u_(x_i)|K=b_i|K.                                      (MCP1)
```

Since every word in the `x_i` may be telescoped through `(MCP1)`, `(MNC1)`
also gives

```text
u_(alpha(x_i))|K=a_i|K.                               (MCP2)
```

By `(MNC4)`, `tK=K`.  Restricting `(MNC5)` to `K` and using
`(MCP1)--(MCP2)` yields

```text
t b_i t^(-1)|K=a_i|K.                                 (MCP3)
```

The `b_i` generate `B` and the `a_i` generate `A`.  Thus `(MCP3)` maps

```text
Fix_B(K)  unitarily onto  Fix_A(K).                   (MCP4)
```

Equivalently, the Reynolds projections `P e_B` and `P e_A` have equal rank.
Combining this equality with `(MNC2)` gives `gamma rank(P)<=0`; hence `P=0`.

If `P=0`, all payload-corner equations disappear.  Taking any exact
representation of the ascending free mapping torus proves the stated perfect
completeness.  The three deletion tests in the claim follow directly from
which implication among `(MCP1)--(MCP4)` is then unavailable.
