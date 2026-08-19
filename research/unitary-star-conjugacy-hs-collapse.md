---
rg: 2
id: unitary-star-conjugacy-hs-collapse
kind: claim
title: An opaque unitary conjugacy star propagates one small hub to every leaf with constant one
---

Let `B,T_1,...,T_m` and `A_1,...,A_m` be arbitrary unitaries in the same
matrix algebra.  No relation whatsoever is assumed among the conjugators
`A_i`.  If

```text
max_i ||T_i-A_i B A_i^*||_2 <= eta,
||B-1||_2 <= delta,
```

then

```text
max_i ||T_i-1||_2 <= eta+delta.                        (STAR-HS)
```

The normalized Hilbert--Schmidt estimate is dimension-free and completely
independent of the words, group elements, or semantics used to produce the
`A_i`.

This is a compiler-lowering principle: when the proof only needs to propagate
smallness from one distinguished opcode to several conjugate opcodes, the
compiler need not preserve the conjugators' multiplication law at all.  It may
output them as opaque transport registers.  A finite multiplication table,
normal-generation word certificates, and approximate representation structure
are all strictly stronger interfaces than `(STAR-HS)` needs.
