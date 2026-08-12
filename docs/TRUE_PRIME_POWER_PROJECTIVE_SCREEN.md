# TRUE: exact projective cellular screening at prime-power level

## Purpose

The compact projective cellular calculations previously used the finite-field
projective plane at prime level.  The next cuspidal level in the
Ash--Yasaki list is `121=11^2`, so a finite-field substitution is no longer
valid: the coefficient set must be the projective plane over

```text
R = Z / p^k Z.
```

The exporter

```text
experiments/sl3_projective_cellular_prime_power_export.g
```

constructs that coefficient action directly over the local ring.  This note
records the exact model, its validation, and what the level-121 calculation
is meant to decide.

## 1. Canonical projective lines over a local ring

Let `R=Z/p^k Z`.  A row `v in R^d` represents a projective line precisely
when it is unimodular, equivalently when at least one coordinate is a unit.
Two such rows represent the same line when they differ by multiplication by
an element of `R^x`.

There is a canonical representative: scan the coordinates from left to
right, take the first unit coordinate, and rescale it to `1`.  This is
well-defined on projective classes because multiplying by a unit neither
changes the first unit position nor the normalized row.

The unit action on unimodular rows is free.  Hence

```text
|P^2(Z/p^k Z)|
  = (p^(3k)-p^(3(k-1))) / (p^k-p^(k-1))
  = p^(2(k-1)) (p^2+p+1).                         (PP1)
```

This count is enforced by the exporter rather than merely reported after the
fact.

## 2. The symmetric-square projective orbit

The HAP complex uses the six-dimensional symmetric-square representation of
`SL_3(Z)`.  Starting from the line of `e_1^2`, the exporter performs an exact
BFS orbit calculation modulo `p^k`, canonically normalizing after every
matrix action.

For odd `p`, the Veronese map from `P^2(R)` to this orbit is injective.  Indeed,
after normalizing a first unit coordinate of `v` to `1`, its diagonal square
coordinate is a unit and the associated mixed coordinates recover every
other coordinate of `v`; the possible factor `2` is a unit because `p` is
odd.  Transitivity of `SL_3(R)` on unimodular rows gives surjectivity.  Thus
the orbit has exactly the cardinality in (PP1).

For every coefficient element appearing in a stabilizer or cellular
boundary, the script computes its permutation of this exact orbit.  A missing
image, repeated image, nonunimodular row, or incorrect orbit cardinality is a
hard error.

## 3. Exact validations

### Prime-level byte comparison

At level `3`, the new local-ring exporter and the previous finite-field
exporter produce byte-for-byte identical boundary files.  Their common
SHA-256 digest is

```text
c29d49368cf799a685f8032d156cdce092fac72f6b87792606c40ccb773dc9e8.
```

This checks action orientation, inverse conventions, stabilizer signs,
boundary ordering, and serialization simultaneously.

### First genuinely nonfield level

At level `9`, formula (PP1) gives

```text
|P^2(Z/9Z)| = 3^2(3^2+3+1) = 117.
```

The exported rational complex has

```text
Q^11 <- Q^16 <- Q^9 <- Q^4,
rank(d1)=10, rank(d2)=6, rank(d3)=3,
d1 d2 = 0, d2 d3 = 0.
```

Consequently

```text
H_0 = Q,  H_1 = 0,  H_2 = 0,  H_3 = Q.           (PP2)
```

The exact summary certificate is

```text
experiments/projective-cellular-n9-summary.json
SHA-256 1a81d7c70b6477ab4c0cfeba0ebd0f4e1f3cf08c8f94aca0e42b3871cdb74ae2.
```

Thus the new path has been checked both against the old implementation where
the latter applies and on a true prime-power ring where it does not.

## 4. The level-121 screen

The batch driver

```text
experiments/msi_sl3_projective_prime_power_screen.sbatch
```

first exports the exact local-ring complex and then invokes the same rational
homology, integral harmonic lattice, and paired-discriminant analyzer used at
prime level.

For `121=11^2`, the export has already certified

```text
|P^2(Z/121Z)| = 11^2(11^2+11+1) = 16093.         (PP3)
```

The decisive output is not merely the size of a selected modular lift.  If
the harmonic lattice is nonzero, compute its compact dual systole `delta_121`
and the spherical template bound `B_121`.  The harmonic plane is relevant to
the localized TRUE gate only when

```text
B_121 delta_121 < 1.                              (PP4)
```

If (PP4) fails, every localized harmonic maximum in the HIL22 reduction is
trivial, just as at prime levels `61`, `79`, and `89`.  If (PP4) holds, level
`121` becomes the next dangerous chart and warrants an exact compact CVP
calculation of its paired-discriminant repair constant.

## 5. Scope

This closes a computational-model gap: composite projective levels can now be
screened without pretending that `Z/p^k Z` is a field.  It does not prove the
uniform family theorem.  The remaining TRUE statement is still a uniform
bound for the paired integral repair of every subthreshold harmonic class,
together with the already-separated nonsmall spherical decoder and the final
character-transfer argument.
