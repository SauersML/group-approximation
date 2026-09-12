---
rg: 2
id: rstar-two-tail-peeling-reduces-fc-char-to-a-dense-kernel
kind: claim
title: Two-tail peeling reduces Fano-cap support to the dense incidence kernel
distinct_from:
  rstar-private-tail-fiberwise-cap-collapse: that assumes three globally occurrence-private coordinates in every row; this permits arbitrary reuse along the peeled part and retains as many as two already-fixed observables per row.
  culf-mastel-rstar-has-no-private-tail-form: that refutes a one-shared-three-private normal form for the hard family; this isolates the strictly smaller residual on which sharing is genuinely obstructive.
  culf-mastel-rstar-halt-model-has-fano-cap-support: that asks for cap support on every row of the published HALT family; this proves that only rows in a computable dense kernel need a new representation theorem.
---

**ESTABLISHED INCIDENCE REDUCTION.**  In a finite `R_*` instance, optionally
mark a set `P` of variables as pinned.  Repeatedly delete any active context
having at least two variables which are not pinned and have active occurrence
degree one.  Delete variables of active degree zero as bookkeeping.  Call
the unique terminal subinstance the **pinned two-tail kernel** `K_2`.

Every context in `K_2` has at least three coordinates which are pinned or
occur in another context of `K_2`.  This kernel is not the ordinary graph
two-core: its deletion threshold is two leaf variables on a four-variable
context.

Let a perfect CE representation of the whole instance be given.  If its
contexts in `K_2` are cap-supported, then it can be modified inside the same
ambient algebra, without changing any kernel observable, so that every
peeled context is cap-supported as well.  In particular:

1. if `K_2` is empty, every perfect CE representation can be replaced by a
   cap-supported one;
2. existence of a cap-supported perfect CE representation of the whole
   instance is equivalent to existence of a perfect CE representation which
   is cap-supported only on `K_2`;
3. if the kernel has `k` rows, exact finite OR need enumerate only `7^k`
   character profiles on the kernel.  The peeled rows receive explicit
   coordinate characters during reconstruction.

With no pinned variables, an empty kernel gives more: the reconstruction may
start from scalars and produces a classical satisfying assignment.  Hence
every classically unsatisfiable `R_*` instance has a nonempty two-tail kernel.

The local threshold is sharp by
`rstar-two-retained-selector-threshold-is-sharp`: a full-support row whose
three coordinates must be retained has its fourth coordinate uniquely forced
by odd parity and cannot be locally shrunk at all.
