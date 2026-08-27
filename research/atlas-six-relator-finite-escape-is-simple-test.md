---
rg: 2
id: atlas-six-relator-finite-escape-is-simple-test
kind: claim
title: Every finite-dimensional six-relator Atlas escape reduces to one larger finite simple marked-A8 overgroup
distinct_from:
  atlas-six-relator-exact-phase-escape-is-a-finite-quotient-test: that converts an exact finite-dimensional escape into a finite quotient retaining a rank-three bridge; this removes the bridge hypothesis, the solvable radical, and all extension data by passing to a simple quotient.
  atlas-q14-finite-quotient-is-simple-overgroup-test: that proves a parallel reduction for the thirty A4 rows, collision q_19243, and q14; this treats the weaker and different five saturated rows plus the centrality word c_19243.
  atlas-six-relator-natural-orbit-mixing-floor: that excludes small natural-orbit permutation components; this reduces arbitrary finite-dimensional mixed solutions, not merely permutation representations, to a finite simple target.
---

Put

```text
Gamma_6=(A8_1*A8_2)/<<s_0,s_11,s_30,s_44,s_55,c_19243>>.      (SST1)
```

The following are equivalent.

1. The six-relator system has an exact finite-dimensional regular-margin
   model with positive five-row linear energy.
2. `Gamma_6` has a nontrivial finite quotient.
3. There are a nonabelian finite simple group `S`, strictly larger than
   `A8`, and injective marked maps

   ```text
   i_1,i_2:A8 -> S                                      (SST2)
   ```

   whose images generate `S` and satisfy the six literal relators.

Every pair in `(SST2)` has distinct labelled copies of

```text
H=GL_3(2)<A8:                                          (SST3)
```

at least one standard `H` bridge survives.  Thus there is no separate
solvable-radical, extension, multiplicity, or bridge-retention case in the
exact finite-dimensional problem.  Its entire residue is one finite-simple
marked-overgroup test.

## Proof

The established finite-quotient criterion gives `1 => 2`: a finite
dimensional image is a finitely generated linear group, so Malcev residual
finiteness separates one positive-energy `H` bridge in a finite quotient.

Suppose conversely that `F` is a nontrivial finite quotient of `Gamma_6`,
replaced by the image.  The kernel of either chart restriction is normal in
the simple group `A8`, so each restriction is trivial or injective.  The
exact one-chart retractions of the six frozen words rule out the asymmetric
cases:

```text
first chart trivial, second injective  => s_0 != 1,
second chart trivial, first injective  => s_11 != 1.   (SST4)
```

Since the two chart images generate `F`, they cannot both be trivial.
Therefore both marked `A8` factors inject into every nontrivial finite
quotient.

Choose a maximal proper normal subgroup `N` of `F` and put `S=F/N`.  The
same argument applies after quotienting: both chart restrictions to `S` are
injective.  In particular `S` is nonabelian; maximality makes it simple, and
the two images generate it.

The group `S` is not `A8`.  Otherwise both marked maps are automorphisms onto
the same subgroup.  The complete inner/outer natural-chart audit has no
automorphism alignment satisfying all six words: the unique alignment
satisfying the five boundary words is the classical one and it fails
`c_19243`.

It remains to show that the bridge required by the phase escape cannot die
when passing to `S`.  If all standard bridges in `(SST3)` died, the two
labelled copies of `H` would agree.  In the regular representation of `S`,
the relative chart frame would then commute with `H`, hence with the fixed
collision subgroup

```text
K_19243=<r,s> ~= S3 < H.
```

The exact `S3` normal form gives, on every such frame,

```text
q_19243=rho(b),
c_19243=rho([p1_12,b]) != I.                          (SST5)
```

This contradicts the defining relation `c_19243=1`.  Hence at least one
`H` bridge survives in `S`.  Its left regular representation restricts to
`[S:A8]` copies of the regular representation on each chart and has positive
five-row energy by the established linear coercivity.  This proves `2 => 3
=> 1`.  The implication `3 => 2` also follows directly from the universal
property of `(SST1)`.

## Consequence

Cross-orbit mixing and continuous relative unitaries do not create an
additional exact finite-dimensional stratum.  If such a mixed exact unitary
exists, a finite simple marked pair `(SST2)` already witnesses it in a
regular representation.  Conversely, ruling out `(SST2)` for every finite
simple overgroup proves that the six-relator matrix zero set has no
positive-energy point.

This is an exact-zero reduction.  It does not by itself provide the uniform
positive normalized-HS gap required by the five-row operator phase lift;
an approximate sequence could still have no exact zero in any dimension.

