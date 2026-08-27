---
rg: 2
id: paired-critical-opposite-roots-return-only-trivially
kind: claim
title: Two exits through the critical opposite root return to the Hecke normalizer only trivially
invalidates:
  - paired-critical-opposite-roots-cancel-whitehead-gauge
artifacts:
  - research/paired-critical-opposite-root-return-proof.md
distinct_from:
  one-nonnormal-dressing-cannot-preserve-moving-full-gram: that proves one nonnormal relative correction cannot preserve the moving full Gram; this checks the first surviving two-exit word and proves its return is the identity.
  compression-preimage-whitehead-preserves-gauge: that treats the next three-root Leavitt preimage Whitehead and finds a conjugated reservoir gauge; this is the shorter rank-one two-exit calculation before any compression prefix is introduced.
  closed-compression-fold-loop-retains-s3-gauge: that closes two binary compression branches through the fold; this treats two occurrences in the single critical opposite-root subgroup.
---

**ESTABLISHED SAME-CHANNEL TWO-EXIT NO-GO.**  Work over
`R=L_(F_2)(1,2)`.  In the actor basis containing coordinates `2,8`, put

```text
d=x_28(1) in L_0,
y_1=x_82(a),  y_2=x_82(b),
c=a+b.                                                   (PCR1)
```

Root additivity gives `y_2y_1=x_82(c)`.  If this two-exit relative
correction returns to the signed Hecke atom normalizer, it normalizes the
underlying constant actor subgroup `L_0`; in particular its conjugate of
`d` must again belong to `L_0`.  On the ordered block `(e_2,e_8)`,

```text
x_82(c) d x_82(c)^(-1)
       = [[1+c,1],[c^2,1+c]].                            (PCR2)
```

Every element of `L_0` is a constant matrix over `F_2`.  The diagonal in
`(PCR2)` therefore forces `c in F_2`.  If `c=1`, `(PCR2)` is the coordinate
swap `[[0,1],[1,0]]`.  This swap is not in `L_0`: every displayed directed
generator of `L_0` fixes `e_2`, because no generator has source coordinate
`2`, whereas the swap moves `e_2`.  Hence `c=0`, and

```text
y_2y_1=1.                                                (PCR3)
```

Thus the first possible pair of genuinely nonnormal exits, when both use
the critical opposite-root channel, returns to `Norm(Q)` only by literal
cancellation.  Its returned normalizer is the identity and cannot cancel a
nontrivial Whitehead reservoir involution.  This does **not** exclude two
exits in different root channels or a longer asymmetric return word.

No Property `(T)`, trace profile, approximation theorem, or
von-Neumann-algebra extension is used.

DERIVATION
paired-critical-opposite-root-return-proof

