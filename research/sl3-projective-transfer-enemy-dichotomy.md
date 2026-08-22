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

The first branch has a further exact restriction.
`subgroup-exact-outliers-do-not-exist` proves that an almost representation
of a property-`(T)` group which is near exact on one fixed finite-index subgroup
is flexibly correctable, by inducing that subgroup representation and
rounding the almost-invariant section range projection.  Hence an SL3
inner-adjoint outlier must stay uniformly far from exact representations on
every fixed finite-index subgroup.  This does not rule such everywhere-inexact
outliers out.

Nor can one descend the nested principal-congruence tower hoping for a first
good fixed level.  `finite-index-correction-is-equivalent-for-kazhdan-groups`
proves that, for each fixed finite-index subgroup, correction of the
restricted tuple is equivalent to correction of the ambient tuple.  An
ambient outlier therefore restricts to a compatible outlier on every fixed
congruence level.  CSP constrains exact representations once found; it does
not break this outlier branch.

The dyadic alternative has one further unconditional restriction.
`exact-dyadic-conductor-band-has-uniform-parahoric-overlap-loss` proves
that a single exact-conductor band loses at least one eighth of its mass
under the native depth shift, uniformly in conductor and multiplicity.
Thus branch 2 must route mass between different conductors over an
unbounded-width profile; it cannot hide inside large same-level
multiplicities.

Clifford classification of only the newest two congruence layers cannot
finish this cross-conductor problem.
`depth-two-clifford-types-form-a-finite-fiber-folner-graph` identifies
those types with a fixed finite orbit set in
`sl_3(Z/4Z)^hat/SL_3(Z/4Z)`.  With the six denominator moves they form a
finite-state skew product over the amenable `A_2` coweight lattice.  The
remaining rigidity must therefore remember unbounded branch history, not
merely the local irreducible type at each depth.

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
