---
rg: 2
id: atlas-full-large-finite-escape-has-simple-local-factor
kind: claim
title: Every faithful full-large finite escape has a constrained nonabelian simple factor
artifacts:
  - experiments/atlas_a4_full_large_simple_factor_kernels.g
  - research/artifacts/atlas-a4-full-large-simple-factor-kernels.json
distinct_from:
  atlas-q96-c144-cycle-has-faithful-a8-quotient: that gives a finite carrier before the fourth large edge; this reduces any hypothetical finite carrier after the full large rectangle to a nonabelian simple target with explicit local images.
  atlas-q96-to-c144-cycle-is-six-generator-finite-vertex-test: that asks directly for a finite quotient preserving all four earlier vertices; this permits the C144 vertex to acquire one of its only two possible order-four kernels after passage to a simple composition factor.
  atlas-a4-finite-quotient-escape-fence: that uses two complete simple A8 chart factors to make every nontrivial finite quotient regular on both charts; this works with the smaller full-large support and proves exactly which solvable local vertices remain injective.
---

Let `Gamma_box` be the six-generator forward/collision presentation with all
four large-rectangle relations.  Suppose `Gamma_box` has a finite quotient
which is faithful on the marked vertices

```text
L=<r,u,t,s> ~= A5,              F'=<r,z,c,u> ~= S3 x S3,
J=<t,s,c> ~= S4,                C=<r,z,b> ~= A4 x A4,
b=st.                                                        (SF-1)
```

Then that finite quotient has a nonabelian simple quotient `S` with the
following exact local behavior:

```text
L -> S injective,        F' -> S injective,        J -> S injective,

ker(C -> S) in {1,V_1,V_2},       |V_1|=|V_2|=4,
C/V_i ~= C3 x A4.                                      (SF-2)
```

In particular

```text
360=lcm(60,36,24) divides |S|.                         (SF-3)
```

The two possible nontrivial `C` kernels are distinct normal Klein four
groups.  Representatives which normally generate them inside `C` are

```text
k_1=(r z^-1 b^-1)^3,
k_2=(r z^-1 b^-1)^4 z r^-1.                           (SF-4)
```

Thus a complete finite-target sieve must allow both the faithful `C144` image
and the two `C3 x A4` images; requiring `C` itself to inject in the simple
factor would discard genuine composition-factor possibilities.
