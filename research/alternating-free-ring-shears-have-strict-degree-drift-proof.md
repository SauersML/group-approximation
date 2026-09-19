---
rg: 2
id: alternating-free-ring-shears-have-strict-degree-drift-proof
kind: route
title: Induct on the unique leading term in each matrix entry
target: alternating-free-ring-shears-have-strict-degree-drift
requires: []
artifacts:
  - experiments/alternating_free_ring_shear_degree.py
---

The formula for `T` follows by multiplication.  The degree profile `(ASD2)`
holds at `n=1`.  Suppose it holds at `n`, and write
`T^n=[[a,b],[c,d]]`.  Right multiplication by `T` gives

```text
a' = a(1+x^2)+b x,       b' = a x+b,
c' = c(1+x^2)+d x,       d' = c x+d.                    (ASD4)
```

The two candidate top degrees in each sum are respectively

```text
a': 2n+2 versus 2n,
b': 2n+1 versus 2n-1,
c': 2n+1 versus 2n-1,
d': 2n   versus 2n-2.
```

They are unequal, so characteristic-two cancellation cannot remove the top
term.  Its coefficient remains one.  This proves `(ASD2)` by induction.

The executable audit represents polynomials by bitsets, multiplies exactly in
`F_2[x]`, and checks every profile and leading coefficient through `n=512`.
The computation is a regression check; the induction is the proof for all
`n`.
