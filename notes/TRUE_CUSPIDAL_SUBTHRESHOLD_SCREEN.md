# Only level 53 has a dangerous harmonic class below 100

Date: 2026-08-11

## Outcome

The compact paired-discriminant model has now been computed at every prime
cuspidal level below `100`:

`p=53,61,79,89.`                                           `(CSS1)`

Let `Q_p^#` be the rank-two harmonic dual lattice, let `delta_p` be its
shortest nonintegral norm, and let `B_p^2` be the largest squared norm of a
degree-three spherical template.  The localization theorem says that only
classes satisfying

`||u|| < 1/B_p`                                            `(CSS2)`

enter the dangerous harmonic part of nonlinear circle repair.  Exact Gauss
reduction gives:

| `p` | `dim_Q H_2` | `delta_p` | `B_p^2` | `B_p^2 delta_p^2` | below threshold? |
| ---: | ---: | ---: | ---: | ---: | :--- |
| 53 | 2 | `0.2670563781...` | 12 | `0.8558293091...` | yes |
| 61 | 2 | `0.3532226523...` | 28 | `3.4934547785...` | no |
| 79 | 2 | `0.3532601379...` | 28 | `3.4941963015...` | no |
| 89 | 2 | `0.7798646007...` | 12 | `7.2982655458...` | no |

Every comparison in the last column is exact: if
`delta_p^2=a_p/q_p` in the exported Gauss basis, the verifier checks

`12a_53<q_53`,
`28a_61>q_61`,
`28a_79>q_79`,
`12a_89>q_89`.                                            `(CSS3)`

Consequently, among all prime cuspidal charts below `100`, level `53` is
the only one with a nonintegral harmonic class in the sub-threshold sector.
For `p=61,79,89`, the harmonic contribution to the localized maximum
`(HIL22)` of `TRUE_HARMONIC_INTEGRAL_LIFT_SEQUENCE.md` is exactly the
trivial value one.  Large integral section norms on those three charts may
matter to a deliberately stronger global decoder, but they cannot witness
failure of the localized harmonic repair theorem.

This materially changes the interpretation of a raw plot of section norms:
the relevant screen is not merely `kappa(p)`, but the pair

`(B_p delta_p, kappa_p)`.                                  `(CSS4)`

The second coordinate needs expensive affine CVP work only when the first
coordinate is below one.

## The originally proposed noncuspidal levels

Exact compact cellular calculations at `p=73` and `p=97` give

`dim_Q H_2(H_73;Q)=dim_Q H_2(H_97;Q)=0`.                  `(CSS5)`

Their complexes have dimensions and ranks

`p=73:  Q^255 <- Q^684 <- Q^636 <- Q^216,`
`        rank(d_1,d_2,d_3)=(254,430,206);`

`p=97:  Q^435 <- Q^1200 <- Q^1136 <- Q^384,`
`        rank(d_1,d_2,d_3)=(434,766,370).`                `(CSS6)`

In each case `d_2 d_1=d_3 d_2=0` in the row-vector convention.  There is
no harmonic plane and hence no harmonic lift norm to optimize.  This is why
the correct next prime after `61` is `79`, not `73`.

## Relation to the all-depth primary computation

The compact screen is independent of, and stronger in a different
direction than, the full-HAP modular section profile.  The latter proves
for all four levels in `(CSS1)` that:

1. both harmonic generators lift through every two-adic depth;
2. the only two-primary correction torsion is `C_4` at `53,61,89` and
   `C_2` at `79`; and
3. one constructive full-plane section modulo `64` has normalized norm
   below `0.60` in every direction.

Thus neither qualitative two-adic nonlifting nor selected-section growth is
visible below `100`.  Equation `(CSS3)` goes further: three of the four
cuspidal harmonic planes do not enter the dangerous localized carry sector
at all.

## What this proves, and what it does not

This is an exact finite-family theorem, not a uniform theorem over all
projective levels.  It proves that the most obvious early denominator
collapse is isolated at `p=53`, and it removes `p=61,79,89` from the
sub-threshold harmonic CVP gate.  It does not rule out later primes with

`B_p delta_p -> 0`,                                        `(CSS7)`

nor does it bound their lift numerators.

The theorem-shaped family target should therefore be stated in the
localized form:

> Prove that every nonzero nonintegral harmonic class satisfying
> `B_p ||u||<1` has an ambient integral lift `z` with
> `||z||<=C||u||`, for a constant independent of the selected projective
> chart.

This target is strictly weaker than bounding an integral section of the
entire harmonic lattice at every level, and is exactly what the nonlinear
localization theorem needs.  The level-`53` certificate already gives

`7.4890553600... <= kappa_53 <= 7.4901774198...`.          `(CSS8)`

So the complete dangerous harmonic sector below `100` has a bounded exact
decoder.  What remains is to prove that no later sub-threshold class has
unbounded paired lift distortion.

## Certificates

The previously committed exact certificates for `p=53,61` are described in
`TRUE_P53_CELLULAR_HARMONIC_DISCRIMINANT.md` and
`TRUE_P61_CELLULAR_HARMONIC_SECTION.md`.  The acyclic certificates are

* `experiments/projective-cellular-p73-summary.json`, SHA-256
  `8cfb54762791bb93377679d39fddd8ec4799a5ade924977bc2121e58dbe62866`;
* `experiments/projective-cellular-p97-summary.json`, SHA-256
  `2247bfbd7d5eb209fc160ec4592400562de1fbdc07362b13c7ed6bfd647dbde5`.

The `p=79,89` compact summaries and reduced section certificates are being
regenerated with overflow-safe exact rank-two generalized eigenvalue
evaluation.  Their shortest-vector data in `(CSS3)` are already exact and
independent of the affine CVP stage.
