---
rg: 2
id: residual-lamp-quotients-handle-monomial-actions
kind: claim
title: Invariant finite lamp quotients preserve stable finiteness under monomial actions
distinct_from:
  rf-lamps-preserve-stable-finiteness-for-arbitrary-actions: that only permutes lamp sites; this also transforms each lamp value by an internal automorphism and tracks the resulting stabilizer actions.
  lef-group-rings-over-stably-finite-rings-are-stably-finite: that allows arbitrary LEF lamps for untwisted actions; this allows twists but requires separating finite quotients invariant under all twisting automorphisms.
---

Let G act on X, and let automorphisms theta_(g,x) of a group A satisfy

    theta_(gh,x)=theta_(g,hx) theta_(h,x).

Define an action on N=direct_sum_X A by moving the x-factor to gx
and applying theta_(g,x) to its value. Put W=N semidirect G.
Suppose A has a family of finite-index normal subgroups M invariant
under every theta_(g,x), with intersection {1}. Then, for every field k,

    k[W] is stably finite iff k[G] is stably finite.

In particular this holds for every finite A with arbitrary such twists,
and for every finitely generated residually finite A with arbitrary such
twists. In the latter case characteristic finite-index subgroups give
the invariant separating family. For untwisted actions it includes
all residually finite A without finite generation.

The finite-lamp proof strengthens the marked-site induction to retain
an arbitrary action of each stabilizer on an auxiliary finite group.
Its base rings are finite extensions k[F semidirect H] of k[H], which
embed in finite matrix rings over k[H] in every characteristic.

In computational language, transporting a stored instruction and
relabeling its internal state still cannot produce a stable inverse
defect over a stably finite base within this class. The action must
send each entire lamp factor to a single lamp factor. Arbitrary actions
mixing different factors, arbitrary twisted LEF lamps, nonsplit group
extensions, and unrestricted wreath products are outside the theorem.
No counterexample to either headline conjecture is supplied.
