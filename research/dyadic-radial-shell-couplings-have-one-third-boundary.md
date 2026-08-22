---
rg: 2
id: dyadic-radial-shell-couplings-have-one-third-boundary
kind: claim
title: Dyadic radial-shell couplings lose at least one third of their mass at the boundary
artifacts:
  - research/artifacts/dyadic-radial-shell-boundary-firewall-2026-08-22.md
distinct_from:
  unamplified-iwahori-sheets-have-two-thirds-defect: that computes the parabolic defect on copies of the single three-sheet action; this treats arbitrary finite radial-shell mixtures and gives a weighted Bass--Serre boundary obstruction.
  dyadic-amplified-edge-random-lifts-exist: that permits arbitrary amplified modular permutation actions and Hamming-almost edge matching; this only refutes the canonical construction from finite mixtures of genuine tree spheres matched orbit by orbit.
---

Let `T` be the 3-regular Bass--Serre tree of

```text
A=C_0 *_B C_1=PSL_2(Z[1/2]),
```

and let `v_0,v_1` be the endpoints of its distinguished edge.  For
`n>=0` put

```text
L_n={z:(d(z,v_0),d(z,v_1))=(n,n+1)},
R_n={z:(d(z,v_0),d(z,v_1))=(n+1,n)}.
```

These are the two depth-`n` edge-Iwahori orbits and each has size `2^n`.
Moreover `L_n` and `R_n` are inequivalent as the oriented `B`-sets for
`n>=1` (the upper parabolic is fixed-point-free on `L_n`, while it fixes
the vertex on its invariant ray in `R_n`).

Take a finite radial `C_0`-set with `a_n` copies of the sphere of radius
`n` about `v_0`, and a finite radial `C_1`-set with `b_n` copies of the
sphere of radius `n` about `v_1`.  Assume the two sets have the same total
cardinality `D`.  If they are coupled only by matching equal oriented
`B`-orbit sheets, at least `D/3` points on each side must be deleted before
their restrictions become isomorphic.

Thus neither balls, annuli, constant-width shell mixtures, nor an
arbitrarily amplified finite radial mixture gives the common-edge coupling
required by `dyadic-amplified-edge-random-lifts-exist`.  This is a firewall
for the canonical finite-quotient-of-the-tree model, not a lower bound for
arbitrary almost-intertwiners of arbitrary finite modular actions.

