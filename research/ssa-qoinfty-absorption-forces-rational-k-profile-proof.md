---
rg: 2
id: ssa-qoinfty-absorption-forces-rational-k-profile-proof
kind: route
title: Compute tensoring with Q directly and remove O-infinity by KK-equivalence
target: ssa-qoinfty-absorption-forces-rational-k-profile
requires: []
---

Write `Q` as an inductive limit of full matrix algebras with unital diagonal
connecting maps. Stability and continuity of K-theory give, for every
separable `D`, without a UCT assumption,

```text
K_i(D tensor Q) ~= K_i(D) tensor Q.                    (1)
```

The Cuntz algebra `O_infinity` is KK-equivalent to `C`, with

```text
K_0(O_infinity)=Z,       [1_(O_infinity)]=1,
K_1(O_infinity)=0.                                        (2)
```

The unit assertion is load-bearing. Toms--Winter, *Strongly
self-absorbing C*-algebras*, Proposition 5.1, says that an SSA UCT algebra
with `K_0=Z` has unit a generator; applied to `O_infinity`, this is `(2)`.
Equivalently, the unital inclusion `C -> O_infinity` is the relevant
KK-equivalence. Exterior product with it gives

```text
K_i(D tensor Q tensor O_infinity)
  ~= K_i(D tensor Q)
  ~= K_i(D) tensor Q.                                  (3)
```

On the other hand, `B` has `K_0(B)=Q`, with unit `1`, and `K_1(B)=0`.
If `B` is `D`-stable, the absorption isomorphism may be chosen approximately
unitarily equivalent to the first-factor embedding `B -> B tensor D`. It
therefore identifies the K-theory and unit in `(3)` with those of `B`,
proving `(RKP)`. The equivalence between a unital embedding `D -> B_omega`
and `D`-stability of `B` for strongly self-absorbing `D` is the standard
McDuff characterization used in STW Problem XIV(2). QED
