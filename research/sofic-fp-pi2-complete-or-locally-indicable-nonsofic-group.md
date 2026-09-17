---
rg: 2
id: sofic-fp-pi2-complete-or-locally-indicable-nonsofic-group
kind: claim
title: Either soficity of finite presentations is Pi-zero-two complete or a finitely presented locally indicable nonsofic group exists
distinct_from:
  sofic-recognition-finite-presentations-is-pi2-complete: that is the completeness question itself, which is open; this is an unconditional disjunction whose second branch settles the orderable nonsofic cells.
  non-rf-hyperbolic-group-or-unique-product-nonsofic-group: that disjunction produces a unique-product nonsofic group from a residual-finiteness failure of a Kazhdan hyperbolic cover; this one produces a finitely presented locally indicable nonsofic group, which has no Kazhdan subgroups, from a failure of the sofic Rice hypothesis.
  compiler-positive-rope-is-not-sofic: that is the open second branch alone.
---

**ESTABLISHED (proposed; rests on the unreviewed `compiler-rope-is-locally-indicable`).**
Derivation: `sofic-fp-pi2-complete-or-locally-indicable-nonsofic-group-proof`.

At least one of the following holds:

- **(a)** `SOFIC_fp` is `Pi^0_2`-complete, which is [[sofic-recognition-finite-presentations-is-pi2-complete]];
- **(b)** for some `e in INF`, the compiler's rope `R_e` is a **finitely presented, locally indicable, nonsofic**
  group.

Branch (b) resolves [[left-orderable-non-sofic-group]] together with its locally indicable and unique-product
variants, with a finitely presented witness.

**Equivalently.**  If every finitely presented locally indicable group is sofic, then `SOFIC_fp` is
`Pi^0_2`-complete.  In the other direction, if `SOFIC_fp` is not `Pi^0_2`-hard, there is a finitely presented
left-orderable nonsofic group.

**What it does not claim.**  It does not claim the converse of either implication.  Hardness of `SOFIC_fp` could be
proved by a different compiler while every `R_e` is sofic.

**Why this is a strict reduction of the orderable cells.**  The only mechanisms on the shelf for the target all
pass through an infinite Kazhdan subgroup, and so sit behind Navas's Question 3.  Here a finitary logic statement
(a) is played against the cell, and (a) is itself open and recorded independently in the graph.  So any proof that
soficity of finite presentations is *not* `Pi^0_2`-hard (for instance a `Delta^0_2` or Boolean-combination
upper bound) would produce the witness.  No Kazhdan subgroup is involved: `R_e` has none
([[twisted-rope-sofic-once-first-rope-sofic]], "What is known").
