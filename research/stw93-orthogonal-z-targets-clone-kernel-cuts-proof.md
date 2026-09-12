---
rg: 2
id: stw93-orthogonal-z-targets-clone-kernel-cuts-proof
kind: route
title: Clone a kernel cut into orthogonal plateau bands of one central Jiang--Su copy
target: stw93-mixed-z-slice-si-forces-infinite-capacity
requires:
  - stw93-singular-trace-needs-finite-central-cuntz-capacity
artifacts:
  - research/artifacts/stw93-mixed-slice-capacity-audit-2026-08-30.md
---

Fix `n`.  Choose a positive contraction `z in Z` with spectrum `[0,1]`.
There are pairwise orthogonal continuous functions

```text
g_1,...,g_n in C_0((0,1))_+
```

of norm one, each equal to one on a nonempty open subinterval of its
support.  Put `f_i=theta(g_i(z))`.  For each `i`, choose a nonzero positive
continuous function `c_i` supported inside the plateau where `g_i=1`.
The unique trace of `Z` is faithful, and `theta` is trace preserving, so

```text
tau_omega(f_i^m)>=tau_omega(theta(c_i(z)))>0
```

for every `m>=1`.  Thus every `f_i` is an `(MSI)`-large target, while
`f_i f_j=0` for `i!=j`.

Apply `(MSI)` to `(e,f_i)` and obtain `s_i in D` with

```text
s_i*s_i=e,                 f_i s_i=s_i.                 (2)
```

For `i!=j`, equation `(2)` gives

```text
s_i* s_j=s_i* f_i f_j s_j=0.
```

Hence the positive elements `b_i=s_i s_i*` are pairwise orthogonal.  Each
`b_i` is Cuntz equivalent to `e`, and their orthogonal sum is a positive
contraction dominated by the unit.  Therefore

```text
n[e]=[b_1]+...+[b_n]=[b_1+...+b_n]<=[1_D].              (3)
```

Since `n` was arbitrary, `e` has infinite central Cuntz capacity.  The same
argument applies to every normalized spectral cut of any `h in I_+`, because
`I` is an ideal.  Now
`stw93-singular-trace-needs-finite-central-cuntz-capacity` shows that no
normalized trace on `D` can charge `I`.  Since `D/I` is a II_1 factor with
its unique normalized trace, every normalized trace on `D` is the canonical
limit trace.

This proof uses no comparison by unknown quasitraces.  That is the point of
the mixed-source `(SI)` witness: it supplies the Cuntz copies directly.
