---
rg: 2
id: global-v4-exit-capacity-is-cross-gram-curvature
kind: claim
title: The global V4 exit-capacity deficit is exactly a leakage-or-cross-Gram curvature floor
distinct_from:
  gram-branching-capacity-with-overlap: that gives the general capacity inequality for arbitrary partial-isometry branches; this substitutes the synchronized V4 source trace and identifies the exact one-quarter curvature that must be paid.
  partial-isometry-gram-is-range-overlap: that identifies one Gram entry with one range overlap; this sums the entries over all context failures and makes them the global shared-context observable.
  globally-conditioned-v4-exit-capacity: that must construct the partial-isometry branches and charge their Gram curvature to defining relators; this proves the analytic endpoint once those branches are supplied.
---

Let `(M,tau)` be finite tracial.  For each context `c` and
`b in {00,01,11}`, let `T_(c,b)` be a partial isometry with source projection

```text
T_(c,b)^*T_(c,b)=F_(c,b),                               (VGC1)
```

where the three `F_(c,b)` are the synchronized V4 failure projections over
the forbidden carrier `P_c`.  Put

```text
P=directSum_c P_c,
q=sum_c tau(P_c),
s=sum_(c,b)tau(F_(c,b))=(5/4)q,
l=sum_(c,b)||(1-P)T_(c,b)||_2^2,
o=sum_((c,b)!=(c',b'))||T_(c,b)^*T_(c',b')||_2^2.       (VGC2)
```

After placing the finitely many contexts in orthogonal bookkeeping summands
(or, equivalently, using the block-diagonal parent projection in a fixed
matrix amplification), `tau(P)=q`.  Then
`gram-branching-capacity-with-overlap` gives

```text
q >= s-2l-o,
2l+o >= q/4.                                            (VGC3)
```

Moreover, by `partial-isometry-gram-is-range-overlap`, if
`E_(c,b)=T_(c,b)T_(c,b)^*`, then every off-diagonal term is exactly

```text
||T_(c,b)^*T_(c',b')||_2^2
 =tau(E_(c,b)E_(c',b')).                                (VGC4)
```

Thus the missing global capacity law has a canonical positive observable:
the one-quarter source surplus must appear either as off-parent leakage or as
cross-Gram overlap of exit ranges.  If the exits are chosen from context-atom
projections, `(VGC4)` is a trace of a product of projections from two
contexts.  It therefore retains shared-variable compatibility and
noncommuting cross-context moments; it does not factor through the scalar
forbidden masses `(tau(P_c))_c`.

Consequently `globally-conditioned-v4-exit-capacity` may be attacked in the
strictly narrower form

```text
l+o <= C E_rel+o(1).                                     (VGC5)
```

Together with `(VGC3)`, this gives `E_rel>=c q-o(1)`.
Constructing the partial isometries with `(VGC1)` and proving `(VGC5)` remain
open; the analytic capacity and payment stages are complete.

