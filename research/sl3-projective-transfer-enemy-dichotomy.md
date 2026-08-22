---
rg: 2
id: sl3-projective-transfer-enemy-dichotomy
kind: claim
title: Every SL3 projective-transfer enemy is either an inner-adjoint outlier or carries macroscopic dyadic congruence mass
distinct_from:
  sl3-odd-correctable-sector-has-uniform-projective-modulus: that closes the purely odd correctable sector; this gives the exhaustive residue after canonical tensor camouflage and includes the uniformly noncorrectable branch.
  fixed-projective-gap-forces-primary-congruence-mass: that quantifies primary mass once an exact lattice correction is available; this first separates enemies according to whether any such correction exists.
  sl3-noncorrectable-lambda-sector-has-no-projective-leak: that conjecturally closes one side of the dichotomy; this establishes only that the two named sides exhaust every enemy.
---

Put

```text
Lambda=SL_3(Z),   Gamma=SL_3(Z[1/2]),
h=diag(2,1,1/2).
```

Suppose `(rho_n,U_n)` refutes projective transfer: its ambient presentation
defect and its projective `Lambda`-energy tend to zero, while

```text
liminf_n (1-|tr([U_n,rho_n(h)])|^2) = epsilon > 0.       (PED1)
```

After tensoring with separating regular finite quotients of `Gamma`, without
changing any defect or projective energy, one may assume that `rho_n` has
the canonical character on `Gamma`.  Passing to a subsequence, exactly one
of the following alternatives holds.

1. **Inner-adjoint outlier.**  The restrictions `rho_n|_Lambda` stay a
   uniform normalized-HS generator distance from every exact
   finite-dimensional representation of `Lambda`.  Equivalently, their
   adjoint tuples stay uniformly far from exact representations inside the
   inner-conjugation locus, modulo scalar phases.
2. **Dyadic correctable carrier.**  There are exact representations
   `sigma_n:Lambda->U(d_n)` with

   ```text
   dist_S(rho_n|_Lambda,sigma_n)->0,                     (PED2)
   ```

   and, in the decomposition of `sigma_n` by minimal congruence conductor,
   irreducibles whose conductor is divisible by `2` occupy a fixed positive
   fraction of `d_n`.

In particular an enemy cannot be both lattice-correctable and asymptotically
supported on odd congruence levels.  This is an exhaustive dichotomy, not a
collapse theorem: the unbounded dyadic carrier and the uniformly
noncorrectable inner-adjoint carrier are the two remaining matrix-coordinate
problems.

The dyadic alternative has one further unconditional restriction.
`exact-dyadic-conductor-band-has-uniform-parahoric-overlap-loss` proves
that a single exact-conductor band loses at least one eighth of its mass
under the native depth shift, uniformly in conductor and multiplicity.
Thus branch 2 must route mass between different conductors over an
unbounded-width profile; it cannot hide inside large same-level
multiplicities.

There is a sharp proof firewall.  In the regular group factor of

```text
<Gamma,t | [t,Lambda]=1>,
```

the stable letter is exactly `Lambda`-central and has maximal projective
energy at `h`, while every arithmetic relation and the canonical actor trace
hold exactly.  Hence neither branch can be eliminated by a dimension-blind
tracial positivity, root-relation, property-(T), Hecke, or finite SOS
argument.  Any completion must use matricial embeddability: dyadic
multiplicity/conductor geometry in branch 2, or regular inner-adjoint
correction in branch 1.
