---
rg: 2
id: computable-proof-system-kleene-interface
kind: claim
title: Formal syntax for computably enumerable proof systems and a Kleene fixed-point operator
distinct_from:
  threshold-free-mf-compiler-equivalence: that node records the semantic fixed-point argument externally; this asks for the reusable Lean syntax and recursion infrastructure itself.
---

Package a computably enumerable proof relation, formulas naming inequalities
of coded words in a fixed finite presentation, restricted soundness for those
formulas, and a recursion theorem producing an index for a program that can
inspect its own code.  No group-theoretic or analytic theorem is missing; this
is the explicit formal-computability interface needed by
`mf-radical-godel-word`.

## Attempts

The existing `reverseKleene_fixedPoint_logic` formalizes only the
proposition-level contradiction and intentionally has no machine-code or proof
enumerator type.  Reusing it would not produce an effective fixed point.  This
interface is deferred until those objects are represented explicitly, rather
than adding an opaque recursion-theorem assumption.
