---
rg: 2
id: power-pair-heisenberg-model-proof
kind: route
title: Scale two finite Heisenberg coordinates and intertwine their regular actions
target: power-pair-phase-hnn-has-finite-heisenberg-mark-models
requires: []
---

Write the Heisenberg group `H_p` as triples `(a,b,c) in F_p^3` with

```text
(a,b,c)(a',b',c')=(a+a',b+b',c+c'+ab').                (PPH2)
```

For `k` nonzero modulo `p`, the map

```text
sigma_k(a,b,c)=(ka,kb,k^2 c)                            (PPH3)
```

is an automorphism.  Let `X=(1,0,0)` and `Y=(0,1,0)`; then
`[X,Y]=(0,0,1)` is nontrivial.  Map `x_1,x_2` to `X,Y` in the first copy of
`B=H_p times H_p`, map `y_1,y_2` to `X,Y` in the second copy, and send any
remaining free generators arbitrarily.  The edge map descends to

```text
delta(h)=(sigma_m(h),sigma_n(h)):H_p -> B,               (PPH4)
```

which is injective.

It remains to implement `(PPH4)` by conjugation in one finite permutation
group.  Let `B` act on itself by left translation and define the permutation

```text
T(u,v)=(sigma_m(u), sigma_n(u)v).                        (PPH5)
```

Both scaling maps are bijective, so `T` is bijective.  For every `h,u,v in
H_p`,

```text
T(h u,v)
 =(sigma_m(h)sigma_m(u),sigma_n(h)sigma_n(u)v)
 =delta(h) T(u,v).                                      (PPH6)
```

Thus `T L_(h,1) T^(-1)=L_(delta(h))`.  Sending the stable letter to `T` and
the base to its left regular permutations gives the required finite
representation.  The commutator mark maps to left translation by
`((0,0,1),1)` and is nontrivial.

The MSI audit `power_pair_heisenberg_finite_model.py` exhausts `(PPH2)--(PPH6)`
for `p=5`, `m=2`, `n=3` on the full `15,625`-point carrier.
