---
rg: 2
id: leavitt-degree3-trivalent-omega-cycle-is-absent-proof
kind: route
title: Solve every unary lift and compare the two ordered residual relators
target: leavitt-degree3-trivalent-omega-cycle-is-absent
requires:
  - leavitt-omega-four-cycle-compiler
  - leavitt-omega-has-an-explicit-distorted-target
---

For an exponent-three cyclic word, expand each of its three
Reidemeister--Schreier relators over the quotient generator `z=t^3`.  A
topology-only enumeration of the `C(7,2)=21` sign paths shows that exactly
fourteen have stable-letter valences `(1,3,3)` up to orbit order.  The unary
relator has the form `Cz=1` after cyclic rotation, and hence determines
`z=C^(-1)`.

For each topology and each of the `7!` packet permutations, the artifact
performs the following operations in the faithful Bergman partial-bijection
chart:

1. reduce `C` in the free product of the three coefficient copies;
2. substitute `z=C^(-1)` into both trivalent relators, preserving their
   stable-letter signs and cyclic order;
3. reduce the resulting coefficient words `R0,R1` exactly;
4. cyclically reduce `R1 R0^(-1)` and compare its sole possible coefficient
   syllable with `h=[c,d]` and `h^(-1)`.

If the comparison succeeded, `R0=R1=1` would force a conjugate of `h` to be
one, giving the required coefficient collapse.  All fourteen shards report

```text
topologies 14
tested 5040
hits 0
```

where each shard owns one sign topology.  Hence the exact total is
`14*5,040=70,560` layouts and there is no such collapse in this finite design
class.  This is an ordered whole-relator test; it does not use the earlier
insufficient unordered common-corner proxy.
