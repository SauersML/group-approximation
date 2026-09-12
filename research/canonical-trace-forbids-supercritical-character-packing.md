---
rg: 2
id: canonical-trace-forbids-supercritical-character-packing
kind: claim
title: Canonical trace gives the sharp ceiling for character packing
root: true
artifacts:
  - research/canonical-trace-forbids-supercritical-character-packing-proof.md
distinct_from:
  finite-overgroup-packing-preserves-hyperlinearity: that proves hyperlinearity permanence after finite Bass--Serre attachment; this gives a direct numerical impossibility theorem at exactly the proposed packing thresholds.
  finite-packet-functoriality-has-positive-regular-profile: that gives a positive regular solution to homogeneous multiplicity equations; this applies the canonical trace directly to conjugate character projections and proves the optimal packing ceiling.
  balanced-marginal-hnn-character-packing: that constructs capacity-sharp local packings; this proves no ordinary group-algebra packing can cross the soundness threshold.
---

Let `G` contain a nontrivial central involution `J`, put

```text
q_-=(1-J)/2,                                            (CTP1)
```

and let `q,e_1,...,e_M` be projections in `C[G]` with

```text
e_i<=q<=q_-.
```

Write `tau` for the canonical group trace and suppose

```text
tau(q)=a>0,             tau(q_-)=h,
sum_i tau(e_i)>=beta a.                                (CTP2)
```

### Separate packing

Suppose that for every `i` there are `K` conjugates of `e_i`, pairwise
orthogonal within that fixed `i`, all lying below `q_-`.  Then

```text
K<=M h/(beta a).                                       (CTP3)
```

### Simultaneous packing

If all `KM` conjugates are pairwise orthogonal across both indices, then

```text
K<=h/(beta a).                                         (CTP4)
```

For the Pauli seed carrier,

```text
a=1/4,                 h=1/2.                          (CTP5)
```

Hence separate packing satisfies

```text
K<=2M/beta,                                             (CTP6)
```

and simultaneous packing satisfies

```text
K<=2/beta.                                              (CTP7)
```

Both bounds are exactly the negations of the proposed supercritical
thresholds.  Therefore no ordinary group presentation in which the seed and
context packet subgroups embed can realize either proposed packing family.
This conclusion is independent of whether a selected noncanonical tracial
model extends to the presentation.

For a shared Boolean contextual system, `(CTP2)` is automatic with the same
soundness constant used by the packing proposal.  Apply soundness to the
finite uniform structural model: the seed has trace `tau(q)=1/4`, each
context assignment has its uniform character weight, and these are exactly
the canonical traces of the corresponding embedded group-algebra
idempotents.  Thus the canonical trace already supplies the dual capacity
certificate.

A viable finite presentation must consequently change the algebra before
the packing count is applied: it must impose a joint relation that prevents
the context packet from embedding, while retaining the marked exact model
needed to keep `J` nontrivial.  Adding more conjugators or finite overgroups
cannot cross `(CTP6)--(CTP7)`.
