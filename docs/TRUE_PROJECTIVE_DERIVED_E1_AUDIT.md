# Positive stabilizer homology is the remaining projective primary problem

Date: 2026-08-11

## Outcome

The zero-th orientation-primary row now splits into local matching blocks
for every odd projective chart.  The derived HAP resolution contains two
additional terms in total degree two:

`E^1_(0,2)` and `E^1_(1,1)`.

An exact mod-two audit at the first six projective primes shows that both
grow with the chart.  They are not fixed-rank bookkeeping that can be
discarded after proving the zero-row theorem.

| `p` | `|P^2(F_p)|` | `dim E^1_(0,2)` | `dim E^1_(1,1)` | `dim E^1_(2,0)` |
| ---: | ---: | ---: | ---: | ---: |
| 3 | 13 | 7 | 8 | 8 |
| 5 | 31 | 9 | 11 | 12 |
| 7 | 57 | 10 | 13 | 18 |
| 11 | 133 | 13 | 18 | 30 |
| 13 | 183 | 15 | 21 | 40 |
| 17 | 307 | 18 | 26 | 58 |

Here `E^1_(2,0)` is the full unsigned degree-two orbit module before its
horizontal cellular differential.  Its orientation-torsion boundary image
is the local repetition matching proved in
`TRUE_PROJECTIVE_PRIMARY_RESIDUAL_MATCHING.md`.  The first two columns are
positive homology of the vertex and edge stabilizers with projective
coefficients.

This does not prove that their eventual contribution to total homology or
integral decoder cost grows.  Higher spectral-sequence differentials may
cancel them by equally local maps.  It does prove that the next task must
compute those induced maps; an argument which simply drops the positive
rows is quantitatively incomplete.

One of the positive horizontal maps can already be computed from the
length-three total complex.  Reducing modulo vertical boundaries gives the
exact map

`H_1(D_8;F_2[X]) -> H_1(S_4;F_2[X])`.                    `(DE1-0)`

| `p` | source | target | outgoing rank | incoming rank | `dim E^2_(1,1)` |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 3 | 8 | 5 | 3 | 5 | 0 |
| 5 | 11 | 7 | 4 | 7 | 0 |
| 7 | 13 | 8 | 5 | 8 | 0 |
| 11 | 18 | 11 | 7 | 11 | 0 |
| 13 | 21 | 13 | 8 | 13 | 0 |
| 17 | 26 | 16 | 10 | 16 | 0 |

The six outgoing ranks equal `(p+3)/2`.  This is an exact finite pattern,
not yet a family theorem.  More importantly, the incoming image from
`E^1_(2,1)` has rank exactly equal to the outgoing kernel in all six cases.
Thus

`E^2_(1,1)=0`                                             `(DE1-2)`

on every audited chart.  Although `(DE1-0)` is neither injective nor
surjective, its growing kernel is completely supplied by the adjacent
two-cell stabilizer row.  The edge-stabilizer term therefore leaves no
middle homology at `E^2` in these cases.  The next proof must establish this
exactness in the subgroup-orbit Shapiro bases for every odd prime; rank data
alone do not supply the uniform splitting norm.

The outer positive term also collapses sharply under the higher Wall
differential.  The complete filtered ranks in the audited range are

| `p` | `E^1_(0,2)` | `im d^1` | `E^2_(0,2)` | `im d^2` | `E^3_(0,2)` | `im d^3` | `E^infinity_(0,2)` |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 3 | 7 | 4 | 3 | 1 | 2 | 0 | 2 |
| 5 | 9 | 5 | 4 | 2 | 2 | 0 | 2 |
| 7 | 10 | 6 | 4 | 2 | 2 | 0 | 2 |
| 11 | 13 | 8 | 5 | 3 | 2 | 0 | 2 |
| 13 | 15 | 9 | 6 | 4 | 2 | 0 | 2 |
| 17 | 18 | 11 | 7 | 5 | 2 | 0 | 2 |

Thus every linearly growing positive stabilizer-homology contribution in
total degree two disappears by `E^3`; the positive filtered residue has
dimension exactly two in all six charts.  The `d^3` image is zero, so this
fixed residue survives to `E^infinity`.  A fixed two-dimensional summand
cannot by itself cause a normalized decoder blow-up.  What remains is to
prove the family statement and obtain bounded local splittings for `d^1`
and `d^2`, not to control a growing positive-row rank.

As an independent check, intersect the total degree-two cycle space with
each cellular filtration step and quotient by the full total boundary
space.  The resulting associated-graded dimensions are

| `p` | `E^infinity_(0,2)` | `E^infinity_(1,1)` | `E^infinity_(2,0)` | total `H_2` |
| ---: | ---: | ---: | ---: | ---: |
| 3 | 2 | 0 | 2 | 4 |
| 5 | 2 | 0 | 2 | 4 |
| 7 | 2 | 0 | 3 | 5 |
| 11 | 2 | 0 | 3 | 5 |
| 13 | 2 | 0 | 4 | 6 |
| 17 | 2 | 0 | 4 | 6 |

Thus the direct filtration calculation agrees with the page-by-page
calculation and locates all remaining growth in the two-cell zero row.  The
positive stabilizer rows contribute exactly two classes, independently of
the six audited levels.

The two surviving positive classes have an even sharper finite description.
On `p=3,5,7`, the first `q=0` stabilizer-resolution generator contains
exactly `p+2` singleton cycles.  One exceptional singleton represents the
first class; every one of the other `p+1` singletons represents the same
second class.  Thus the quotient pattern is

`{exceptional point} disjointUnion {p+1 ordinary points} -> F_2^2`,

with the two fibres mapping to the two standard basis vectors.  Sparse
quotient bases choose one singleton from each fibre, so both surviving
classes have support one.  In the projective orbit ordering these begin at
the coordinate-square lines, whose vertex stabilizer is `C_2 x C_2`.

This identifies the likely all-prime local template, but does not yet bound
the chains which identify the `p+1` ordinary singletons.  An arbitrary
row-echelon preimage can be long.  The next quantitative step is therefore
to exhibit bounded local relations or a uniformly bounded decoder for this
two-fibre quotient, rather than to compute more homology ranks.  The exact
singleton profile is in
`experiments/projective-derived-q0-singletons.tsv`, with SHA-256
`bb8bdb5a4a20dc68be72cadae192aa983dd9708622f19a3b5f11fbc1d40a775b`.

There is already one prime-independent local relation.  In total
degree three, the same four `(resolution generator, coefficient
coordinate)` pairs have boundary

`e_1+e_8`                                                `(DE1-4)`

in the first `q=0` generator for every odd projective prime.  Both endpoints
are ordinary singleton cycles.  This is an exact theorem, not an
extrapolation from the six levels: all coefficient points in the chain are
reductions of fixed rational projective lines, and direct evaluation in
HAP's integral group-ring resolution gives precisely the two displayed
rational endpoints.  Reduction modulo any odd prime proves `(DE1-4)`.

The exact rational verifier is
`experiments/sl3_projective_q0_relation_exact.g`; its stdout certificate is
`experiments/sl3-projective-q0-relation-exact.txt`, with SHA-256
`6d6e924f94c7af378a0a49fc923eafbf97a3eed8b1afab605664532598249219`.
The finite-chart verifier
`experiments/sl3_projective_q0_relation.py` independently checks the raw
specialized matrices; its compact audit is
`experiments/projective-derived-q0-relation.tsv`, with SHA-256
`9ff88cf113f302d5c3d008cd1c5127ff4d4f030c8635bfe3c00b56ff4bb2b8b3`.

The ordinary `p+1` points are the Veronese image of a projective line; the
exceptional point lies off it.  The Wall-compatible relation graph on this
line is now exact: one fixed generator gives `t <-> 2-t`, and the four-term
chain joins its two fixed points `1,infinity`.  These relations split the
matching-difference subspace with norm `sqrt(2)` for every odd prime.  See
`TRUE_PROJECTIVE_SINGLETON_MATCHING_DECODER.md`.  The live object is the
smaller pair-orbit quotient, not the original projective line.  Arbitrary
`SL_3` translates are still unavailable because the full coefficient action
does not preserve one filtered generator.

## Exact extraction

HAP's total resolution has bidegrees

`F_2=A_(0,2) directSum A_(1,1) directSum A_(2,0)`

with generator multiplicities `6,2,2`.  Its degree-three term supplies the
incoming vertical boundaries.  For each `q`, reduce the block preserving
`q` modulo two and put

`dim E^1_(q,s)=dim A_(q,s)-rank(delta_v:A_(q,s)->A_(q,s-1))`
`                         -rank(delta_v:A_(q,s+1)->A_(q,s)).`

All ranks in the table are exact sparse `F_2` ranks.  The raw HAP exporter
now writes `d1,d2,d3`; the analyzer
`experiments/sl3_projective_derived_e1.py` extracts the blocks from the
fixed `pair2Quad` decomposition.  The compact result table is
`experiments/projective-derived-e1.tsv`, with SHA-256
`51dd694e50beed2c9801abe9e9c370f1513e46889984ecc4167e3b40b097435c`.

For `(DE1-0)`, the analyzer takes the left kernel of the vertical
`A_(1,1)->A_(1,0)` block, applies the horizontal
`A_(1,1)->A_(0,1)` block, and measures its rank modulo the row space of
vertical boundaries in `A_(0,1)`.  It verifies exactly that source vertical
boundaries are cycles and that horizontal images are target vertical cycles.
The compact table is
`experiments/projective-derived-e1-horizontal.tsv`, with SHA-256
`6a72a9221ad458232e97ee2a8127e67ee8dd8e2da3d0a933574394acc3fd1b81`.

For the incoming rank it takes vertical cycles in `A_(2,1)`, applies the
horizontal block into `A_(1,1)`, and measures the image modulo target
vertical boundaries.  Determining this image does not require quotienting by
the as-yet-unexported incoming vertical boundaries in the source.  The chain
identity puts the image inside the outgoing kernel; equality of their ranks
proves `(DE1-2)` exactly.

The `d^2` calculation uses corrected pairs in
`A_(2,1) directSum A_(1,2)`: their boundary is required to vanish in
cellular degrees two and one, and the remaining degree-zero component is
measured modulo the vertical and `d^1` denominator.  For `d^3`, add the
`A_(3,0)` component and quotient further by the `d^2` image.  These are
direct filtered-complex calculations from `d2,d3`; no unexported degree-four
boundary is needed to determine either image.

The analyzer also computes the induced filtration on total homology
directly.  For each `q`, it takes total cycles supported in cellular degrees
at most `q`, adjoins the full row space of `d3`, and measures the rank gain.
Successive differences give the displayed `E^infinity` grading.  This avoids
assuming that the visible higher-page ranks exhaust total homology.

In characteristic two it additionally enumerates zero rows in the first
`q=0` generator and tests each singleton class against the full total
boundary space.  It verifies that the first two singleton classes are
independent and records the unique two-bit class label of every remaining
singleton.

## Next exact task

The middle of the second complex in the following display is exact on the
first six charts, and the first complex plus its higher differential leaves
only a two-dimensional residue.  Prove these observations uniformly and
classify their integral splitting norms:

`E^1_(1,2) -> E^1_(0,2)`,

`E^1_(2,1) -> E^1_(1,1) -> E^1_(0,1)`.               `(DE1-1)`

The existing length-three HAP object contains all filtered images which can
reach total degree two.  Full homology in the source terms would require one
further vertical stabilizer boundary, but it is not needed for the image
ranks just computed.  Only the groups `S_4,D_8,D_12` are involved.

Once those maps are known, compute their local block types under the natural
projective orbit classification.  A uniformly split matching, as in the
zero row, removes the remaining derived-primary concern.  A family of small
singular values or high-distance quotient classes would instead identify a
real obstruction to the TRUE route.

The vertical stabilizer complexes themselves are already uniformly
decodable: they split orthogonally over transitive coefficient orbits
`H/L`, leaving only the local fibres `H_s(L;Z_chi|L)`.  See
`TRUE_VERTICAL_STABILIZER_DECODER_SPLITTING.md`.  Thus the requested local
block classification is exactly the remaining arithmetic content, rather
than a problem with the chosen free stabilizer resolutions.
