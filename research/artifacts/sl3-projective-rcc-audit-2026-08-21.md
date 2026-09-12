# Audit of the SL3 projective-transfer / RCC lane

## Narrowest root-facing theorem

For `Lambda=SL_3(Z) <= Gamma=SL_3(Z[1/p])`, the narrowest theorem needed
by the centralizer-HNN route is qualitative relative-commutant collapse in
regular tracial matrix ultraproducts:

```text
pi(Lambda)' cap M = pi(Gamma)' cap M.
```

Because both groups are perfect, qualitative projective transfer is
equivalent to ordinary RCC. The all-assignment affine inequality `(PRT1)`
in `projective-commutant-transfer-for-arithmetic-pair` is a stronger
quantitative theorem than the root reduction consumes.

## Exact co-density is not an approximation theorem

The pair `SL_3(Z) < SL_3(Z) x A_fin` has equality of images in every exact
finite-dimensional unitary representation, yet its canonical hyperlinear
regular model has a maximal RCC leak from the second direct factor. The
proof is recorded in `exact-codensity-does-not-imply-matricial-rcc`.
Therefore the established exact trace-square gap cannot be promoted by
compactness alone. Any successful arithmetic proof must exploit coupling
between the `SL_3(Z)` subgroup and the denominator generator.

## The current p=3 exact-face closure has two open seams

First, the inference

```text
asymptotic invariance under every fixed coweight shift => flat/Haar profile
```

is false on growing finite scale lattices. Triangular Folner profiles have
vanishing fixed-shift total-variation defect and vanishing atoms while
remaining total-variation distance `1/4` from Haar. The explicit proof is
`fixed-shift-invariance-no-flat-profile-proof`. The min-overlap argument may
still prove fixed-shift invariance/delocalization, but not uniqueness of a
flat profile.

Second, `flux-identification-lemma-protocol-2026-08-21` correctly records
that the canonical parahoric band transports have not yet been identified
with the normalized Weil--Maslov intertwiners. Stone--von Neumann
uniqueness leaves scalar freedom on each edge; the closed product of those
scalars is precisely the flux that must be computed. A model calculation
of the Weil flux does not by itself prove that the actual transporter in
the RCC problem carries that normalization.

Thus `lambda-exact-face-closes-at-p-three` remains an open claim. Its
underlying RCC target is not refuted; only the present closure route is.

## Honest surviving targets

1. Prove arithmetic RCC directly for regular-trace microstates, without
   asserting a unique flat profile.
2. Add a genuine scale-mixing/entropy estimate strong enough to rule out
   nonuniform Folner profiles, then prove the missing transporter/Weil
   dictionary.
3. Produce a CE arithmetic action or other regular-profile model giving a
   counterexample; the general direct-product example shows this is not
   excluded by exact co-density.

