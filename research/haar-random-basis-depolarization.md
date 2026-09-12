---
rg: 2
id: haar-random-basis-depolarization
kind: claim
title: Random intermediate-basis dephasing is exactly a one over d plus one depolarizing channel
invalidates: [markovization-via-random-intermediate-basis]
artifacts:
  - research/artifacts/hyperlinear-extreme-breakthroughs-2026-08-18.md
---

Fix unitaries `U,V`, endpoint bases `B_1,B_3`, and a Haar-random intermediate
basis `B`. Put

```text
A = B* U B_1,
C = B_3* V B,
D = B_3* V U B_1,
P_X = |X|^2 entrywise.
```

**Theorem.** Exactly,

```text
E_B[P_C P_A]
 = (J + P_D)/(d+1)
 = (d/(d+1))(J/d) + (1/(d+1)) P_D.
```

Thus averaging over a fresh random intermediate basis does not make dephasing
multiplicative: it depolarizes the composed transition and preserves only a
`1/(d+1)` fraction of the coherent transition matrix. The same coefficient as
`covariant-separable-relative-signal-ceiling` is not accidental; both are Haar
second-moment identities.
