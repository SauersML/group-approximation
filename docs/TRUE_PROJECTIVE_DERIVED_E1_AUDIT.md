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

## Next exact task

Compute the `E^1` horizontal maps

`E^1_(1,2) -> E^1_(0,2)`,

`E^1_(2,1) -> E^1_(1,1) -> E^1_(0,1)`.               `(DE1-1)`

The existing length-three HAP object contains the chain-level horizontal
blocks in `(DE1-1)`, but homology in the source terms requires one further
vertical stabilizer boundary.  HAP truncates `FreeGResolution` at the
three-dimensional proper complex, so that boundary must be obtained from
the fixed finite-stabilizer resolutions directly.  Only the groups
`S_4,D_8,D_12` are involved.

Once those maps are known, compute their local block types under the natural
projective orbit classification.  A uniformly split matching, as in the
zero row, removes the remaining derived-primary concern.  A family of small
singular values or high-distance quotient classes would instead identify a
real obstruction to the TRUE route.
