---
rg: 2
id: odd-root-central-d8-order-proof
kind: route
title: Compare the order of an odd root with its central-sign conjugate
target: odd-root-cannot-drive-central-d8-actuator
requires:
  - affine-leavitt-active-root-character-orbits-are-aperiodic
---

Centrality of the commutator in `(ODA1)` gives

```text
s w s^(-1)=J^(-1)w=Jw.                                  (ODA3)
```

Conjugation preserves the equation `w^p=1`, while `J` commutes with `w`.
Therefore

```text
1=(sws^(-1))^p=(Jw)^p=J^p w^p=J,                       (ODA4)
```

because `p` is odd and `J^2=1`.  The affine application follows from the
characteristic statement recorded in
`affine-leavitt-active-root-character-orbits-are-aperiodic`.
