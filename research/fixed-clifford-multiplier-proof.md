---
rg: 2
id: fixed-clifford-multiplier-proof
kind: route
title: Push out the congruence extension by the invariant character and restrict it to the root cycles
target: fixed-clifford-multiplier-is-nonsplit-root-double-cover
requires:
  - fixed-clifford-projective-dyadic-tower
---

The invariance of `chi_a` implies that `ker(chi_a)` is normal in `G_a`.
Moreover, for `g in G_a` and `x in L_a`,

```text
chi_a([g,x])=chi_a(gxg^(-1))chi_a(x)^(-1)=1.
```

Thus the image `L_a/ker(chi_a)=<z>` is central in `E_a`, proving `(FCM3)`.
The ordinary factor set of a section takes values in `L_a`; pushing it out
by `chi_a` gives `(FCM4)`. A projective representation with this factor set
is the same thing as a linear representation of the pushout extension on
which `z` acts by `-1`, proving `(FCM5)`.

For the upper root lift, the nilpotence `E_12^2=0` gives the exact identity

```text
(I+E_12)^n=I+nE_12.
```

Taking `n=2^(a-1)` modulo `2^a` yields

```text
u^(2^(a-1))=I+2^(a-1)E_12.
```

The kernel element on the right has coordinates `(A,B,C)=(0,1,0)`, so
`chi_a=-1` and its image in `E_a` is `z`. The same calculation with
`E_21` gives the lower-root identity. Since the root image downstairs has
order `2^(a-1)`, either lift has order exactly `2^a`; this proves
`(FCM6)`--`(FCM7)`. A split central extension restricts to a split extension
on every subgroup, so this nonsplit restriction also proves that the global
cohomology class is nonzero.

If `z=-I`, functional calculus applied to `(FCM6)` gives `(FCM8)` and the
odd-root description. The squaring assertion is the elementary map

```text
exp(2 pi i (2j+1)/2^a)
  |-> exp(2 pi i (2j+1)/2^(a-1)).
```

Finally restrict the left regular representation of `E_a` to the cyclic
root subgroup `C_(2^a)`. Every character occurs with multiplicity
`[E_a:C_(2^a)]`. Cutting by the central idempotent `(1-z)/2` retains exactly
the odd characters, still with the same multiplicity. Splitting each old odd
character equally over its two odd square roots therefore preserves the
normalized root spectral measure with no discarded mass. This proves the
claimed cyclic-marginal zero-loss recursion and no more: the two root lifts
do not commute, so their separate spectral measures do not determine a
representation of `E_a` or an edge constituent.
