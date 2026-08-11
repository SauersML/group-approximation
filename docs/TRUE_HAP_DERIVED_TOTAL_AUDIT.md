# HAP already implements the required derived stabilizer total complex

Date: 2026-08-11

## Outcome

The next construction proposed in
`TRUE_TWO_PRIMARY_CELLULAR_DERIVED_AUDIT.md` already exists inside HAP.
For the proper `SL_3(Z)` complex `P=ContractibleGcomplex("SL(3,Z)")`,

`FreeGResolution(P,3)`

is the Wall/perturbation total complex formed from fixed free resolutions of
the cell stabilizers.  Moreover,

`ResolutionArithmeticGroup("SL(3,Z)",3)`

is defined by exactly that call.  Thus the large free resolution already
used by `sl3_projective_h2_export.g` is the desired derived integral model;
there is no second total complex left to construct.

This does **not** prove a uniform circle-repair theorem.  It removes an
implementation ambiguity and identifies the remaining map exactly: expose
and control the augmentation between the filtered total complex and its
compact signed-coinvariant row, including its bounded-primary lifting
defect.

## Exact bidegrees

Write the total complex as

`F_n = directSum_(q+s=n) A_(q,s)`,

where `q` is cellular degree and `s` is degree in a free resolution of the
corresponding finite stabilizer.  HAP retains this decomposition through
`pair2Quad` and `quad2Pair`.

The compact complex has orbit dimensions

`(1,1,2,1)`,

while the derived free resolution has dimensions

`(1,4,10,20)`.

The exact bidegree multiplicities are

| total degree | bidegrees `(q,s)` and multiplicities |
| ---: | --- |
| 0 | `(0,0):1` |
| 1 | `(0,1):3`, `(1,0):1` |
| 2 | `(0,2):6`, `(1,1):2`, `(2,0):2` |
| 3 | `(0,3):10`, `(1,2):3`, `(2,1):6`, `(3,0):1` |

In particular, the ten degree-two free generators used in the projective
Shapiro calculation split into six vertex-stabilizer generators, two
edge-stabilizer generators, and the two compact 2-cell generators.  At
level `53` this becomes the already-computed `10*2863=28630` dimensional
degree-two module.

## Finite stabilizer templates

There are only five cell-orbit templates through degree three:

| cell `(q,r)` | order | GAP identifier | orientation values |
| --- | ---: | --- | --- |
| `(0,1)` | 24 | `[24,12]` | `{1}` |
| `(1,1)` | 8 | `[8,3]` | `{-1,1}` |
| `(2,1)` | 24 | `[24,12]` | `{-1,1}` |
| `(2,2)` | 12 | `[12,4]` | `{-1,1}` |
| `(3,1)` | 24 | `[24,12]` | `{-1,1}` |

Consequently all vertical templates and every perturbation component are
fixed independently of the projective prime.  Inverting `24` kills the
positive stabilizer homology.  Integrally, the unresolved discrepancy is
therefore confined to the `2`- and `3`-primary sectors, with bounded
exponent; its rank may still grow with the chart.

## Uniform propagation is explicit

Every boundary coefficient in the free resolution is an integral group
element with sign.  After specialization to any finite permutation action,
each term becomes a signed permutation matrix.  Counting terms therefore
gives a chart-independent Schur bound.

The exact source-column and target-row maxima are

| differential | maximum column sum | maximum row sum | squared Schur bound |
| ---: | ---: | ---: | ---: |
| `partial_1` | 2 | 8 | 16 |
| `partial_2` | 35 | 28 | 980 |
| `partial_3` | 306 | 101 | 30906 |

Hence the specialized operator norms are bounded by `4`, `sqrt(980)`, and
`sqrt(30906)` respectively for every chart.  These constants are coarse,
but they prove that constructing the derived model introduces no hidden
growth in the real operator norms.  Any remaining failure is arithmetic,
not analytic propagation.

## Canonical map and the live obstruction

The total differential is assembled from components

`Del_k:A_(q,s) -> A_(q-k,s+k-1)`.

The `Del_0` component is the vertical stabilizer differential, `Del_1` on
the zero row is the cellular boundary, and the higher `Del_k` are the Wall
perturbation corrections.  Augmenting each stabilizer resolution and
killing `s>0` gives the canonical map from the total complex to the proper
cellular complex.  The higher rows make this a derived, rather than naive,
coinvariant comparison.

Over `Z[1/24]`, finite-stabilizer averaging supplies a bounded inverse up to
homotopy.  Over `Z`, this inverse need not preserve the lattice.  The live
question is therefore:

> Can the `2`- and `3`-primary augmentation defect be decoded with a
> normalized Euclidean norm bounded independently of the projective chart?

At level `53`, the immediate computational target is no longer “build the
derived complex.”  It is to use the existing filtered decomposition to lift
the two certified compact harmonic classes into the `28630`-coordinate
total complex and measure the best integral section.  Failure should be
reported as an explicit class in a positive stabilizer-homology row.

The zero-th orientation-primary boundary has since been split uniformly,
but the first derived audit shows that the positive rows are substantial:
at `p=3,5,7,11,13,17`, the exact dimensions of
`(E^1_(0,2),E^1_(1,1))` are respectively
`(7,8),(9,11),(10,13),(13,18),(15,21),(18,26)`.  The next computation is
therefore the induced horizontal differential between these groups, not
another zero-row orbit calculation.  See
`TRUE_PROJECTIVE_DERIVED_E1_AUDIT.md`.

The reproducible metadata exporter is
`experiments/sl3_derived_resolution_audit.g`; its exact MSI output is
`experiments/sl3-derived-resolution-audit.txt`, with SHA-256
`55bc75aaaab2228ce6d5776a8d7a44fb70ed448c13a79a29ff09b55500614048`.

The zero-th row of this filtered augmentation now admits one exact uniform
cancellation.  The transfer from the first degree-two `S_4` cell to the
degree-one `D_8` cell is a permutation isomorphism on every signed
orientation-`C_2` orbit summand, with norm-one inverse.  This removes that
zero-row pair before studying the augmentation defect, but it does not touch
the positive stabilizer-resolution bidegrees listed above.  See
`TRUE_SL3_PRIMARY_TRANSFER_SPLITTING.md`.

The vertical part of those positive bidegrees is nevertheless uniformly
decodable.  For a fixed finite stabilizer `H`, restriction of any finite
coefficient action decomposes into transitive `H/L`-orbits.  The specialized
free stabilizer resolution is the orthogonal direct sum of finitely many
fixed subgroup templates, so integral vertical boundary sections have a
chart-independent Euclidean norm.  After this reduction the only possible
primary obstruction is the horizontal Wall differential on the local
groups `H_s(L;Z_chi|L)` and its coupling to the zero row.  See
`TRUE_VERTICAL_STABILIZER_DECODER_SPLITTING.md`.
