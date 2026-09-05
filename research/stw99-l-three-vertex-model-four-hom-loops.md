---
rg: 2
id: stw99-l-three-vertex-model-four-hom-loops
kind: claim
title: Four explicit circle actions on the three-vertex graph algebra span its Hom(K1,K0) block
artifacts:
  - research/artifacts/stw99-l-six-kirchberg-loops-2026-09-05.md
---

Let `C = C*(E(1,1,2))`, `e_C = [1_C]`, `b = [p_1]`, and put

```text
U_1 = R_1 R_3^*,     U_2 = R_2 R_3^*.
```

Then `{[U_1], [U_2]}` is an INTEGRAL basis of `K_1(C) = Z^2` -- not merely
a finite-index subgroup, and with no unnamed graph `K_1` representative
involved.  The four circle actions

```text
h_1(z) = g_{13, z^{-1}},   h_2(z) = g_{11, z},
h_3(z) = g_{23, z^{-1}},   h_4(z) = g_{21, z}
```

have invariants

| loop | Delta([U_1]) | Delta([U_2]) | Delta on K_0(C) |
| --- | --- | --- | --- |
| h_1 | e_C | 0 | 0 |
| h_2 | b | 0 | 0 |
| h_3 | 0 | e_C | 0 |
| h_4 | 0 | b | 0 |

so their classes are a `Z`-basis of the rank-four summand
`Hom(K_1(C), K_0(C))` of the splitting in
`stw99-l-pi1-aut-splits-into-two-hom-groups`, and they lie in the
kernel of the projection to the other summand.
