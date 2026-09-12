---
rg: 2
id: involution-covariance-is-four-times-binary-consistency-proof
kind: route
title: Expand the two spectral projections and use consistency equals half squared distance
target: involution-covariance-is-four-times-binary-consistency
requires:
  - consistency-defect-is-state-dependent-distance
---

Put

```text
D=(S-T)/2=P_S(+)-P_T(+).
```

Since the minus projections are complements,

```text
P_S(-)-P_T(-)=-D.
```

Therefore the squared state-dependent distance between the two binary PVMs is

```text
sdDistSq(P_S,P_T)
 = ||D||_2^2+||-D||_2^2
 = 2||D||_2^2
 = (1/2)||S-T||_2^2.                                  (1)
```

The established projective consistency-distance identity gives

```text
sdDistSq(P_S,P_T)=2 consDefect(P_S,P_T).               (2)
```

Comparing `(1)` and `(2)` yields

```text
||S-T||_2^2=4 consDefect(P_S,P_T).
```

Apply this separately to the two involutions generating the atlas `S_3` to
obtain the final statement and divide `1/128` by four to get the consistency
threshold `1/512`.
