---
rg: 2
id: depth-shifted-regular-overlap-is-exactly-one-sixteenth
kind: claim
title: The two depth-shifted regular congruence representations have exactly one-sixteenth common mass
distinct_from:
  lambda-exact-face-of-the-collapse-closes: that uses a coarse order-four witness to obtain a regular-type Kazhdan floor; this computes the complete kernel-join quotient and improves the common fraction from at most one quarter to exactly one sixteenth.
  two-power-sector-conjugator-dichotomy: that says near intertwiners are all-or-nothing by property T; this computes the finite-level invariant subspace on the regular module.
  fixed-shift-invariance-does-not-force-flat-profile: that concerns arbitrary scale-spread isotypic weights; this exact fraction is a Plancherel/regular-module statement and does not exclude those weights.
---

Let `Lambda_0=<A>` and `B=hAh^(-1)` be the tuples in
`two-power-sector-conjugator-dichotomy`.  At level `2^a`, `a>=2` (the audit of 2026-08-21 checked `a = 2` as well; at `a = 1` the packet has order `8`), put

```text
K_A(a)={gamma in Lambda_0: gamma=1 mod 2^a},
K_B(a)={gamma in Lambda_0: h gamma h^(-1)=1 mod 2^a},
Q_A=Lambda_0/K_A(a),
Q_B=Lambda_0/K_B(a).                                  (DSO1)
```

Then

```text
|Q_A|=|Q_B|,
[K_A(a)K_B(a):K_A(a)]=16.                             (DSO2)
```

More precisely, the image of `K_B(a)` in `Q_A` is exactly

```text
U_a={ [1 x z; 0 1 y; 0 0 1] mod 2^a :
      x,y in 2^(a-1) Z/2^a,
      z   in 2^(a-2) Z/2^a },                         (DSO3)
```

which has order `2*2*4=16`.

For any finite-index normal subgroups `K_A,K_B` of a group `G`, let

```text
pi_A=r_A Reg(G/K_A),
pi_B=r_B Reg(G/K_B).
```

Their common irreducibles are exactly the irreducibles of
`G/(K_AK_B)`, and the maximal common subrepresentation has dimension

```text
min(r_A,r_B) |G/(K_AK_B)|.                             (DSO4)
```

The restrictions of the level-`a` left regular congruence representation to
the `A`- and `B`-copies have equal multiplicity because of the first equation
in `(DSO2)`.  Therefore their maximal common dimension fraction is exactly

```text
|Lambda_0/(K_AK_B)|/|Q_A|=1/16.                       (DSO5)
```

The same formula holds at every mixed level `2^a q`, `q` odd: the odd
kernel is common to both maps, while CRT leaves the 16-element packet
`(DSO3)` on the two-primary leg.

Consequently, if `V` is a unitary matrix and `Inv` is the exact intertwiner
space between the two regular restrictions, then

```text
dist_2(V,Inv)^2 >= 15/16.                              (DSO6)
```

Property `(T)` converts this to the uniform generator-defect floor

```text
max_i ||pi_A(A_i)V-V pi_B(B_i)||_2
   >= epsilon_0 sqrt(15)/4.                            (DSO7)
```

This closes the regular/Plancherel two-primary and mixed sectors with a
sharper constant.  It does not close arbitrary genuine congruence
representations: the trivial representation has common fraction one, and in
general the exact overlap is the sum of the minima of the two isotypic
dimension weights over common irreducibles.  A canonical-profile argument
must still exclude the recorded scale-spread non-Plancherel escape before
`(DSO7)` can be applied without the regular-type hypothesis.
