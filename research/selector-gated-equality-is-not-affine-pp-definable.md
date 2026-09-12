---
rg: 2
id: selector-gated-equality-is-not-affine-pp-definable
kind: claim
title: Selector-gated payload equality is not affine pp-definable
distinct_from:
  affine-auxiliary-control-flow-barrier: that treats one-hot selection and binary AND; this isolates the exact selector-payload implication and the priority-decoded cross-context equality relation needed by the ZPC transducer.
  priority-decoded-contexts-are-not-glued-by-raw-gate-equality: that gives operator countermodels to unconditional raw-gate equality; this proves that even arbitrary hidden parity auxiliaries cannot exactly express the desired conditional scalar relation.
  zpc-context-mismatch-transducer: that permits genuinely projective or source-specific mechanisms; this rules out a universal commuting parity pp-gadget only.
---

**ESTABLISHED.**  In scalar bit notation, selector-gated equality is the
relation

```text
R_gate={(s,g,h): s=0, or g=h}.                           (SGE1)
```

It is not the projection of the solution set of any finite system of affine
`F_2` parity equations, regardless of how many existential auxiliary bits
are added.

The same obstruction applies directly to priority decoding.  For three odd
selector bits `s=(s_1,s_2,s_3)`, payload bits `g=(g_1,g_2,g_3)`, and
`p(s)=min{a:s_a=1}`, the graph

```text
y=g_(p(s)),                  s_1+s_2+s_3=1              (SGE2)
```

is non-affine.  More strongly, the relation saying that two independently
priority-decoded contexts have the same decoded bit is non-affine even on
canonical singleton configurations, where every inactive predicated payload
is zero.

Consequently no exact ZPC context-mismatch transducer made solely from binary
LCS parity equations and commuting existential control bits can enforce the
needed selector-payload coupling while preserving all three singleton branch
configurations.  A surviving construction must use source-specific affine
degeneracy, a genuinely projective central-sign packet with no relevant
scalar sector, or another noncommutative mechanism.  Ordinary hidden parity
bits do not suffice.

This is a pp-definability fence, not a refutation of
`zpc-context-mismatch-transducer`: the perfect ZPC strategy may be genuinely
noncommutative, and a central-sign LCS gadget need not admit the scalar
characters used below.

