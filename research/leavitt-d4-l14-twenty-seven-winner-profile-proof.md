---
rg: 2
id: leavitt-d4-l14-twenty-seven-winner-profile-proof
kind: route
title: Rank and cyclically classify the twenty-seven-winner profile
target: leavitt-d4-l14-twenty-seven-winner-profile-has-three-classes
requires:
  - leavitt-d4-latin-triangle-reduction
---

MSI job `16687076` ran

```text
--length 14 --profile=---+++--++++++ --balanced-only
--show-rank=9 --classify-rank=9
```

and returned

```text
rank 9: 27, rank 10: 882, rank 11: 3222,
rank 12: 12546, rank 13: 20061, rank 14: 11862.

I(0;131): 9
I(0;311): 9
N(0;131): 9
```

All systems counted are carrier-balanced.  Cyclic rotation of each target
face is quotiented exactly as in the preceding length-fourteen censuses;
global inversion is not used.  The compiler reconstructs the four corner
orbits directly from the sign word and stores one emitted representative of
each class.  Independent boundary analysis remains open.
