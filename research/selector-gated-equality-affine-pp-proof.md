---
rg: 2
id: selector-gated-equality-affine-pp-proof
kind: route
title: Take ternary XORs of gated and priority singleton solutions
target: selector-gated-equality-is-not-affine-pp-definable
requires:
  - affine-auxiliary-control-flow-barrier
  - odd-selector-priority-decoding
---

The solution set of an affine parity system in visible variables `x` and
auxiliaries `z` is an affine subspace.  Its projection to `x` is affine too,
so every existential parity relation is closed under ternary XOR.

For `(SGE1)`, the three points

```text
(0,0,0),          (0,1,0),          (1,0,0)             (SGE3)
```

are valid.  Their ternary XOR is `(1,1,0)`, which is invalid.  Hence gated
payload equality has no affine pp-definition.

For the priority graph, use the three canonical singleton configurations

```text
s=e_1, g=(0,0,0), y=0,
s=e_2, g=(0,1,0), y=1,
s=e_3, g=(0,0,0), y=0.                                  (SGE4)
```

All inactive payloads are zero.  Their XOR has

```text
s=(1,1,1),        g=(0,1,0),        y=1.                (SGE5)
```

But priority chooses the first active branch, whose payload is `g_1=0`, so
`(SGE5)` is outside the graph.

Finally make this a literal two-context mismatch example.  In the second
context use selector `e_1` in all three configurations and give its first
payload respectively `0,1,0`.  Each of the three pairs has equal decoded
bits.  Their ternary XOR leaves the second selector equal to `e_1` and its
decoded payload equal to `1`, whereas the first XOR context decodes to `0`
by `(SGE5)`.  Thus even the equality relation between two priority outputs is
not affine on the singleton-completeness menu.

Any affine relation containing all three completeness configurations must
contain their invalid XOR.  Adding hidden parity variables cannot change
this because projection preserves affinity.

