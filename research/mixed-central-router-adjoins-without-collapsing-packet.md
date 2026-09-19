---
rg: 2
id: mixed-central-router-adjoins-without-collapsing-packet
kind: claim
title: The mixed-central router adjoins to a Schur relative pair without collapsing its packet
distinct_from:
  mixed-central-cnot-completes-relative-rank-one-router: that constructs the finite router and its mass split abstractly; this identifies its control pair with literal Schur packet words and proves algebraic completeness of the attachment.
  full-center-hnn-transport-cancels-schur-multiplicity: that glues entire selector centers and admits stationary dimension flow; this amalgamates only the named relative pair and marked sign, leaving selectors context-local.
---

Let `P` be one finite Schur packet, let `a,b` be a named corrected relative
pair of involutions, put `K=[a,b]`, and retain the packet's marked central
involution `J`.  Assume `K` is central in the finite relative-pair subgroup,
as it is for the class-two predicate packets.

Let `G(K,J)` be the four-generator mixed-central router of
`mixed-central-cnot-completes-relative-rank-one-router`, identifying its
control generators with the same `a,b`.  Form

```text
P *_<a,b,K,J> G(K,J),                                  (MCA1)
```

then add the HNN stable letter implementing the router automorphism on
`G(K,J)`.  Both Bass--Serre steps embed their base vertex groups.  In
particular, the original packet `P` embeds, its selector sectors are not
identified with another context, and no allowed character is deleted.

Every exact representation of `P` with `J=-I` induces to a unitary
representation of `(MCA1)` and then of the HNN extension; centrality keeps
`J=-I` in the induced representation.  Thus adjoining all finitely many
routers preserves a witness that the common marked sign is nontrivial.

On a forbidden packet atom, the identified words `a,b` are the relative
Pauli pair, so `K=-1`; the router's equations `(MCR4)--(MCR5)` apply literally.
On a sector where that pair commutes, `K=+1` and the router retains its
allowed rank-two marked block.  Hence the attachment adds the fixed-density
flag and active/exit CNOT without duplicating the predicate's extra Pauli
qubit.

This is an algebraic completeness theorem.  In approximate finite-dimensional
models, the two finite vertex packets can be flexibly exactified and their
shared four-generator edge compared with fixed finite-group transport cost.
Coordinating that cost across all three endpoint contexts and E5 levels is
the remaining quantitative return theorem.
