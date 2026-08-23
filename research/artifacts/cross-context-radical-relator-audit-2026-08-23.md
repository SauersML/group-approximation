# Cross-context radical-relator audit — 2026-08-23

## Outcome

The finite conjugacy question and the proposed downstream soundness argument
have opposite answers.

1. **The designated outside-word tuples do align exactly.**  Two opposite
   lifted `GL_2(F_2)` shears fix the two shared raw coordinates word for word,
   on every selector sector, including satisfying sectors.  The prescribed
   central twist is zero.
2. **The two endpoint words do not both enter the reset multiplicity
   commutant.**  A nondegenerate codimension-one reset hyperplane has only one
   orthogonal radical line.  In the crossed chart that line is
   `<r_(a,0)+r_(a,1)>`, so neither basis word centralizes the reset packet.

The first result materially reduces
`covariant-model-satisfies-cross-context-radical-relators`.  The second result
invalidates `three-chart-return-from-cross-context-relators`; establishing
the completeness claim would therefore not close the hyperlinear goal by
that route.

## Exact stabilizer calculation

Write the predicate compiler space as `F_2^2 tensor V_inner`, with outer
hyperbolic form `H`, and take

```text
r_(a,0)=e_0 tensor k_a,       r_(a,1)=e_1 tensor k_a,
ell_3=ell_1+ell_2.
```

Use the chart order

```text
alpha=ell_1,        beta=ell_3,        gamma=ell_2.
```

The two transvections

```text
G_0=[[1,1],[0,1]],             G_1=[[1,0],[1,1]]
```

preserve `H` and obey

```text
G_0 e_0=e_0,       G_0^T ell_3=ell_1,
G_1 e_1=e_1,       G_1^T ell_2=ell_3.
```

After extending them by the identity on the inner and odd chart
coordinates, these are congruences of the complete affine chart pencils for
every selector value.  Choose one common-sector reset witness `phi_beta` and
put

```text
phi_alpha=G_0^T phi_beta,       phi_gamma=G_1^T phi_beta.
```

This makes the reset hyperplanes equivariant.  The phase-corrected packet
lifts introduce no root factor: `G_0` fixes every generator in the `e_0`
half and `G_1` fixes every generator in the `e_1` half, while the raw words
are products only of generators in the corresponding fixed half.

For an outside vector, decompose `r=w+cq` along the odd radical `q` with
`w` in the reset hyperplane.  The congruences carry `q,w,c` to their target
values.  Across all marked atoms, the projected `w` vectors are independent
and isotropic, hence their commuting Pauli tuple has uniform joint spectral
multiplicity.  This verifies simultaneous conjugacy, not merely equality of
one-word traces.

Finally,

```text
(ell_1-ell_3)(r_(a,0))=0,
(ell_3-ell_2)(r_(a,1))=0,
```

so the fixed central exponents in the two proposed relators vanish.

## Exhaustive certificate

The executable certificate is
`experiments/cross_context_radical_relator_audit.py`.  One exact MSI run on
Sioux `acn112`, using one Python process, checked:

```text
predicates_checked:          4
marked_atoms_checked:        8
comparison_blocks_checked:  80
satisfying_blocks_checked:   64
forbidden_blocks_checked:    16
central_twists_checked:      144
result: all designated outside-word tuples are exactly S3-conjugate
```

The four predicates are `C13/C14`, `C17`, the C18 child guard, and the C18
four-bit residual.  Every assertion is over `F_2`; no floating-point
threshold or randomized search occurs.

## Reset-commutant obstruction

At a forbidden atom, the odd chart form has a one-dimensional radical and
every admissible reset hyperplane `W` is nondegenerate.  Therefore

```text
W^perp=rad(B_ell).
```

For `ell=ell_3`, restriction of `ell_3` to the raw radical plane takes value
one on each basis vector, so

```text
rad(B_(ell_3))=<r_(a,0)+r_(a,1)>.
```

Thus neither `r_(a,0)` nor `r_(a,1)` commutes with the reset subgroup.  This
is also visible in the certificate: every designated word has a nonzero
projected Pauli vector on the crossed-chart reset spin block.  Transport
cannot change the conclusion because conjugation preserves commutators.

The sentence in `three-chart-return-from-cross-context-relators` claiming
that both transported endpoint projections lie in the fresh multiplicity
algebra is therefore false.  Exact cross-context word equality does not
repair that type of mismatch; a successor route needs a different reset or a
non-character decoder whose two endpoint observables genuinely live on one
common carrier.
