---
rg: 2
title: STW XCI complete-graph tensor-anchor audit (2026-08-30)
kind: artifact
---

# Result

The noncomplete graph-product theorem leaves complete defining graphs because
their complement has no nonsingleton component. The maximal immediate
positive class supplied by current tensor permanence is nevertheless broad:
a countable complete graph product of C-star-simple vertex groups is selfless
as soon as one reduced vertex algebra is completely selfless. Every other
vertex group may be nonexact and need not itself be known selfless.

For finite complete graphs, if every vertex algebra is completely selfless,
the product is completely selfless. For an ordinary selfless anchor, the same
ordinary conclusion holds when the complementary vertex algebras are exact.

# Proof audit

A complete graph product is the restricted direct sum of its vertex groups.
After fixing v_0 it splits as

    G_(v_0) times direct_sum_(v not equal v_0) G_v.

De la Harpe's product and inductive-limit permanence makes the complementary
restricted direct sum C-star-simple whenever all of its coordinates are
C-star-simple. Modern unique-trace theory then makes its canonical trace the
unique trace.

Gao--Junge--Kunnawalkam Elayavalli--Patchell--Robert,
[arXiv:2607.20361](https://arxiv.org/abs/2607.20361), Theorem 1.3(iii),
says that tensoring a completely selfless state with the unique trace of a
simple algebra preserves selflessness without exactness of the second
algebra. Applied to the displayed group splitting, this proves the result.
The exact-second-factor clause gives the ordinary-anchor variant.

For the finite all-completely-selfless upgrade, Ozawa,
[arXiv:2508.07938v7](https://arxiv.org/abs/2508.07938), Theorem 11,
preserves complete selflessness under binary minimal tensor products, so
finite iteration applies.

The reverse simplicity implication is elementary but important. Every vertex
group is a direct factor. A proper ideal in one reduced vertex algebra,
followed by its quotient map tensored with the identity of the complementary
factor, produces a proper quotient of the full reduced algebra. Thus the
complete graph product is C-star-simple exactly when all vertex groups are.

# Exact boundary

The anchor hypothesis is not automatic for complete graphs. With one vertex,
the assertion that every C-star-simple group supplies such an anchor would
already solve STW XCI. No descent of selflessness from G times F_2 to G is
used: a trace slice is completely positive rather than multiplicative.
Consequently this claim enlarges the positive complete-graph class without
asserting the open universal case.
