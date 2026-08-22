---
rg: 2
id: edgeful-one-ghost-escape-avoids-term-recurrence
kind: claim
title: The edgeful one-ghost Hadamard cell changes exactly one logical marginal
distinct_from:
  rstar-hadamard-escape-violates-term-c4: that proves an odd-parity assignment pair necessarily changes at least two marginals and repeats the full term; this chooses a Hamming-distance-one pair in the edgeful relation.
  one-binary-marginal-block-escape: that preserves one selected marginal but does not control how many other logical marginals acquire the escaped coefficient; this makes that support singleton.
---

Use `one-binary-marginal-block-escape` on two rank-one coordinates labelled
by assignments `a,b in R_edge` at Hamming distance one, say in coordinate
`y`.  On the escaped plane the coefficient of
`h_r h_s^(-1)E_rs` in logical marginal `X_z` is

```text
((-1)^(a_z)-(-1)^(b_z))/2.                              (EHE1)
```

It is nonzero exactly for `z=y`.  Therefore the cell fixes the other three
marginals simultaneously, moves two genuine assignment atoms outside the
finite root block, and places its escaped full support terms in exactly one
logical marginal.

Choose one representative from each adjoint pair of coefficient equations
and use fresh phase generators for different escape planes.  Then the full
endpoint word contributed by this plane is not repeated merely because the
other logical marginals must also be synchronized.  In particular the
two-piece `C(4)` obstruction of
`rstar-hadamard-escape-violates-term-c4` is absent at this endpoint.  A
subdivided equality chain still makes the first intermediate term recurrent,
but the endpoint term is not a piece, so their pairing relator is not a
product of two pieces.

This is only a local escape from that obstruction.  It does not verify the
remaining coefficient-link `C(4)-T(4)` conditions, select Fano-cap supports
in the perfect-gap family, or solve simultaneous return holonomy.
