---
rg: 2
id: nonhyperlinear-from-marked-swap-star
kind: route
title: Contradict the two canonical word traces with the marked binary star floor
target: non-hyperlinear-group
requires:
  - central-marked-swap-star-has-two-word-trace-floor
  - marked-swap-star-compiler
---

Let `y,j_0,j_1` be supplied by the compiler and put `h=j_0j_1`.  Exact
completeness makes `y,h,yh` nonidentity.  If the group were hyperlinear,
canonical microstates would satisfy

```text
tr(y)->0,                 tr(h)->0,                 tr(yh)->0.
```

The finite-matrix decoder and the marked-star trace theorem instead give

```text
Re(tr(h)-tr(yh))>=1/4(1-tr(y))-o(1)->1/4,
```

a contradiction.  Hence the compiled group is non-hyperlinear.
