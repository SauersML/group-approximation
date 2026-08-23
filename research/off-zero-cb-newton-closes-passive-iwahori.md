---
rg: 2
id: off-zero-cb-newton-closes-passive-iwahori
kind: route
title: A mixed L2/operator-norm normal splitting integrates the passive Iwahori tuple
target: invariant-bs-block-cut-leaves-a-passive-coordinate-basin
requires:
  - regular-short-low-frequency-bs-source-hull-is-sublinear
  - low-rank-reflection-surgery-preserves-the-exact-bs-core
  - right-displacement-reynolds-scalar-cb-complete
  - regular-reynolds-bad-levels-cannot-be-quarantined
  - passive-core-quotient-has-relative-rational-h2
  - passive-iwahori-off-zero-cb-normal-splitting
---

After the established slow length-frequency cut, enlarge the active
`BS(1,4)`-invariant hull by the two exits and the finite Gram-surgery
support.  Its relative rank is `o(1)`.  Block cutting and polar reflection
surgery cost `o(1)` in normalized HS, retain an exact restricted BS core on
the passive complement, and make the involution/inversion rows exact.  By
the definition of the cut, the two remaining cubic rows have operator norm
`theta_n -> 0` there.  It remains to integrate those two rows.

We record the Newton estimate because it is the reason both norms in
`passive-iwahori-off-zero-cb-normal-splitting` are load-bearing.  Fixed word
length and a fixed smooth retraction `Ret_x` of the involution/inversion
constraint manifold give one universal `L` such that, for `p=2,infinity`,

```text
||F(Ret_x Z)-F(x)-DF_x Z||_p
   <= L ||Z||_op ||Z||_p.                              (PCN1)
```

The same estimate holds for two nearby base points after increasing `L` by
a fixed factor.  Put

```text
y_k=F(x_k),              Z_k=-G_(x_k)y_k,
x_(k+1)=Ret_(x_k)(Z_k).                                (PCN2)
```

By `(PCB3)--(PCB4)` and `(PCN1)`, while
`||y_k||_op<=theta_0`,

```text
||y_(k+1)||_op
 <= (C_0+L C_infinity^2)||y_k||_op^2,                 (PCN3)

||y_(k+1)||_2
 <= (C_0+L C_infinity C_2)||y_k||_op ||y_k||_2,       (PCN4)

||Z_k||_op <= C_infinity||y_k||_op,
||Z_k||_2  <= C_2||y_k||_2.                           (PCN5)
```

Choose a universal `theta_*<=theta_0` so both coefficients times
`theta_*` are at most `1/4`.  For all sufficiently large `n`, the passive
tuple starts below `theta_*`.  Equations `(PCN3)--(PCN4)` make the operator
residual quadratically convergent and the HS residual geometrically
convergent.  The correction series converges in both norms to a tuple
`x_infinity` on the same exact-core constraint manifold, with

```text
F(x_infinity)=0,

||x_0-x_infinity||_2 <= 2 C_2 ||F(x_0)||_2,
||x_0-x_infinity||_op <= 2 C_infinity ||F(x_0)||_op.  (PCN6)
```

Thus the passive tuple itself enters the operator-norm coordinate basin of
the exact endpoint produced by the iteration; no congruence label or
endpoint orbit was selected in advance.  Reattach any exact realization of
the `o(d)` active block using the allowed flexible padding.  The block cut,
reflection surgery, and `(PCN6)` tend to zero in normalized HS, proving all
four conclusions of the target claim.

This proof also identifies why the known uniform tangent gap does not yet
close the target.  Its `2 -> 2` inverse controls the last line of `(PCN5)`
but gives no bound on `||Z_k||_op`; without that bound the Taylor remainder
in `(PCN1)` can be of first order in normalized HS on a small carrier.  The
remaining passive theorem is therefore the off-zero completely bounded
normal splitting, not another congruence-level conductor or a scalar
endpoint fingerprint.
