---
rg: 2
id: qutrit-line-hnn-router-has-full-source-but-coincident-range
kind: claim
title: The qutrit line HNN router has full source but coincident target ranges
artifacts:
  - research/qutrit-line-hnn-free-polar-proof.md
distinct_from:
  qutrit-any-finite-router-polar-carries-at-most-half-residual: that proves every finite-head polar loses at least half the selected source; this is the minimal infinite Bass--Serre router and its individual phase polars are full-source.
  qutrit-external-cyclic-router-selects-only-one-hidden-third: that realizes the same star inside a finite C3-cubed head and exposes a hidden character cut; this replaces the hidden finite direction by a free C3 direction.
  amenable-edge-hnn-preserves-hyperlinearity: that gives the general permanence firewall; this computes the exact qutrit polar geometry to which it applies.
---

Let `C=<j,z> isomorphic to C_3^2`, let
`chi_a(j)=omega`, `chi_a(z)=omega^a`, and put
`p_a=z_(C,chi_a)`. Form the HNN extension

```text
Lambda=<C,U | U^(-1) z U=j^(-1)>.                      (QHR1)
```

Britton normal form gives

```text
C intersect U C U^(-1)=<z>,
U^(-1)<z>U=<j>.
```

Consequently

```text
p_b U p_a !=0  if and only if  b=2.                    (QHR2)
```

Unlike the finite cyclic router, every surviving block has a full polar.
If

```text
p_2 U p_a=W_a |p_2 U p_a|,
```

then in `L(Lambda)`

```text
W_a^*W_a=p_a,             W_aW_a^*=p_2               (QHR3)
```

for all `a in F_3`. The reason is that, after fixing the common
`j`-character, the two vertex quotients are free copies of `C_3`.
Their character projections are free projections of equal normalized trace
`1/3` and hence are in general position.

Thus the two selected phases `a=0,1` each have a genuine full-source
partial isometry onto the complementary phase. Coupled to either D8 branch,

```text
||W_aV_eta||_2^2=||p_aV_eta||_2^2=1/288.               (QHR4)
```

This is the smallest positive escape from the hidden-third firewall.

It still does not give a nonhyperlinearity certificate. The two target
ranges coincide exactly:

```text
W_0W_0^*=p_2=W_1W_1^*.
```

They are not two orthogonal copies packed into `p_2`. Moreover `(QHR1)`
is an HNN extension over a finite, hence amenable, edge group. Attaching the
same stable letter to any hyperlinear base preserves hyperlinearity.
Therefore the full-source phase star is compatible with canonical
microstates.

The next load-bearing object cannot be another independent amenable-edge
router. It must impose a joint relation on the relative unitary
`W_0^*W_1:p_1->p_0` inside an infinite nonamenable vertex, or derive a
typed residual constraint which separates the two otherwise coincident
target occurrences.
