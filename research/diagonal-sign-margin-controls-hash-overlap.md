---
rg: 2
id: diagonal-sign-margin-controls-hash-overlap
kind: claim
title: Diagonal sign margin controls terminal-to-sample hash overlap without boundary cost
distinct_from:
  compression-signs-alone-do-not-fix-joint-multiplicity: that shows signs with fixed poor margin do not control multiplicity; this proves the quantitative positive statement when the margin error vanishes
  two-code-character-cut-recenters-to-one-coordinate: that aligns one two-leaf cut directly; this controls the simultaneous overlap mismatch of a whole sampled hash
---

Let `(f_a)` be a PVM and let `h_s(a) in {+1,-1}` be prescribed signs for
sample positions `s=1,...,t`.  Put

```text
H_s=sum_a h_s(a)f_a,
X_s=sum_a f_aQ_sf_a,
a_s=||X_s-H_s||_2.                                      (DSM1)
```

Let `T_1,...,T_t` be commuting reflections and put
`b_s=||T_s-Q_s||_2`.  If `(e_y)` is their joint sign PVM and

```text
f_y=sum_(a:(h_1(a),...,h_t(a))=y) f_a,
```

then the off-label overlap satisfies

```text
Gamma=sum_(y!=z)tau(f_y e_z)
 <=(1/2)sum_(s=1)^t(a_s+b_s).                           (DSM2)
```

No term involving `||Q_s-X_s||_2`, the unknown physical cut boundary,
appears.

Indeed the probability, in trace, that the `s`th corrected sign disagrees
with the terminal sign is

```text
(1/2)(1-tau(H_sT_s)).                                   (DSM3)
```

Because `H_s` is block diagonal while `Q_s-X_s` is block off-diagonal,
`tau(H_s(Q_s-X_s))=0`.  Hence `(DSM3)` is at most
`(a_s+b_s)/2`.  A joint label mismatch occurs in at least one sampled
coordinate, so the union bound gives `(DSM2)`.

## Attempts

Bounding `||H_s-Q_s||_2` directly reintroduces the unknown terminal
boundary.  Only the tracial mismatch is needed, and its off-diagonal term
vanishes exactly.  This trace cancellation is what survives the conference-
matrix counterexample: there `a_s` is order one.
