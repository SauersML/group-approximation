---
rg: 2
id: low-rank-reflection-surgery-preserves-the-exact-bs-core
kind: claim
title: Joint Gram reflection surgery leaves the BS core exact and localizes every new relator defect
distinct_from:
  two-exit-gram-swap-builds-low-rank-involution-surgery: that constructs the replacement reflection and its support bound; this propagates that support bound through every Iwahori relator while keeping the exact BS coordinates fixed.
  bs14-low-rank-boundary-surgery-preserves-the-regular-face: that cuts an already exposed exact dilation and polarizes its compression; this is the reverse local replacement on a supplied joint source/exit Gram cell.
  bs14-residual-invariant-hull-has-unbounded-packet-loss: that rules out taking a BS-invariant hull of an arbitrary source; this proves no invariant hull is needed merely to control the metric and fixed-word rank after a reflection surgery.
---

**ESTABLISHED.**  Let `(R,S)` be an exact finite-dimensional `BS(1,4)`
core and let `X_0` be a reflection.  Suppose an exact joint exit-Gram cell
of source rank `r` is completed by
`two-exit-gram-swap-builds-low-rank-involution-surgery`, producing a
reflection `X_1` which equals `X_0` off a subspace `L` with

```text
ell=dim L<=8r.                                         (LRS1)
```

Keep `R` and `S` literally unchanged.  Then the BS relation remains exact,
`X_1^2=1` is exact, and for every fixed word `w` containing `q` occurrences
of `X`,

```text
rank(w(X_1,R,S)-w(X_0,R,S))<=q ell,
||w(X_1,R,S)-w(X_0,R,S)||_F<=2q sqrt(ell).             (LRS2)
```

Thus if `r/d->0`, all inversion and cubic defect changes vanish in
normalized Hilbert--Schmidt norm.  The operation never takes the
`R,S`-invariant hull of `L`; word telescoping visits only the finitely many
translates present in the fixed presentation rows.

To prove `(LRS2)`, telescope the two word evaluations one occurrence of
`X` at a time.  Every summand is a unitary left/right translate of
`X_1-X_0`, whose rank is at most `ell` and whose Frobenius norm is at most
`2sqrt(ell)`.  Rank subadditivity and the triangle inequality finish the
proof.

This is a metric surgery theorem, not endpoint exactification.  It leaves
the core exact and the active cell reflection exact, but any remaining
low-rank inversion/cubic rows must still be realized by a genuine global
endpoint.
