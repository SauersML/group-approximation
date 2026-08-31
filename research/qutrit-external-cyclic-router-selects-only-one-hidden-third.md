---
rg: 2
id: qutrit-external-cyclic-router-selects-only-one-hidden-third
kind: claim
title: The minimal external qutrit router gives two-to-one incidence but carries only one hidden third
artifacts:
  - research/qutrit-external-cyclic-router-hidden-third-proof.md
distinct_from:
  qutrit-jacobson-central-line-twist-is-similarity-impossible: that excludes a central-to-leaf twist inside the entire Jacobson matrix host; this constructs the smallest external finite twist and computes its exact failure after coupling to the D8 residual polar.
  qutrit-two-to-one-phase-graph-requires-central-line-twist: that identifies the abstract intersection pattern; this realizes it by a signed cyclic automorphism and resolves every source and target Gram projection.
  finite-overgroup-packing-preserves-hyperlinearity: that gives the general finite Bass--Serre firewall; this exhibits the concrete one-third loss responsible for the firewall in the qutrit polar.
---

Let

```text
E=<j,z,w> isomorphic to C_3^3,       C=<j,z>,
chi_a(j)=omega,                      chi_a(z)=omega^a,
p_a=z_(C,chi_a).
```

The signed cyclic automorphism

```text
theta(j)=w^(-1),        theta(w)=z,        theta(z)=j^(-1)
```

has order three. Put `B=E semidirect_theta <g>`, where
`g x g^(-1)=theta(x)`, and set `U=g^(-1)`. Then

```text
C intersect U C U^(-1)=<z>,
U^(-1)<z>U=<j>.
```

Thus this finite group realizes the asymmetric leaf-to-central line twist
which is impossible over the Jacobson coefficient algebra. Its qutrit
blocks are the exact desired star:

```text
p_b U p_a != 0  if and only if  b=2,
||p_2 U p_a||_2^2=1/27                    for every a. (QER1)
```

In particular, the two selected phases `p_0,p_1` both have the unique
target phase `p_2`.

However, the router carries only one hidden third of each source. The
operators

```text
Y_a=p_2 U p_a
```

are partial isometries between character atoms of `E`. Their initial and
final projections have characters

| projection | `j` | `z` | `w` |
|---|---:|---:|---:|
| `Y_a^*Y_a` | `omega` | `omega^a` | `omega^2` |
| `Y_aY_a^*` | `omega` | `omega^2` | `omega^a` |

and trace `1/27`. Hence `Y_0+Y_1` uses one of the three `w`-phases in
each selected source and two of the three `w`-phases in the complementary
target. It does not transport all of `p_0+p_1` into `p_2`.

This remains exact after the natural coupling to the Jacobson D8 polar.
Identify `w` with either second-qutrit Pauli generator commuting with
`C`, so `E<=F_q`. For each sign branch `V_eta`,

```text
||Y_a V_eta||_2^2=1/864,
||(Y_0+Y_1)V_eta||_2^2=1/432
                         =(1/3)||(p_0+p_1)V_eta||_2^2. (QER2)
```

The routed mass is also exactly two thirds of the native complementary
mass `||p_2V_eta||_2^2=1/288`. Thus the external star consumes the hidden
third which its line intersection introduces; it creates no Hall overload.

Finally, adjoining `B` along `E` is a finite-overgroup amalgam. It
preserves hyperlinearity of any hyperlinear base and supplies canonical
finite induced extensions of its microstates. Therefore this minimal
external router is an exact positive incidence gadget but not a
nonhyperlinearity certificate. A load-bearing continuation must constrain
at least two such hidden-phase carriers jointly by a relation outside finite
Bass--Serre covariance, or use a multi-word analytic compression whose
interference removes the hidden `w` cut.
