# The first zero-row orientation-primary block splits with norm one

Date: 2026-08-11

## Outcome

The zero-th stabilizer-homology row in the compact projective carry model can
be reduced further.  In the fixed HAP cellular resolution, the degree-one
cell stabilizer is

`H ~= D_8`,

the first degree-two cell stabilizer is

`K ~= S_4`,

and `H<K` has index three.  Their orientation characters are compatible,
and the three boundary elements of the first degree-two cell form a right
transversal for `H` in `K`.

For every finite `K`-set `X`, the induced boundary map is an isomorphism

`T_K(X) -> T_H(X)`                                           `(PTS1)`

between the orientation-torsion summands of the signed integral
coinvariants.  In the natural orbit bases, `(PTS1)` is a permutation matrix
over `F_2`.  It therefore has a right inverse of normalized `L2` norm exactly
one, independently of `X`.

Consequently the entire degree-one orientation-primary sector in ordinary
signed coinvariants and an equal part of the first degree-two sector form a
uniformly contractible pair.  They cannot contain the bad
high-covering-radius binary code inside the zero-th row.

This does not remove all two-primary arithmetic.  The ordinary signed orbit
complex is only the zero-th row of the derived stabilizer total complex; its
positive stabilizer-homology rows remain.  Within the zero-th row, the live
primary block is concentrated in the second degree-two cell and degree
three.

## Signed orbit modules

Let `J` be a finite group with orientation character

`chi_J:J->{+1,-1}`,

and define the signed coinvariant module of a finite `J`-set `X` by

`M_J(X)=Z_chi tensor_(Z[J]) Z[X]`.                              `(PTS2)`

For a transitive orbit `J/L`, `(PTS2)` is

`Z` if `chi_J|_L=1`,
`Z/2Z` otherwise.                                               `(PTS3)`

Indeed all orbit coordinates are identified up to the orientation sign.  A
negative element of the stabilizer gives `e=-e`, while in its absence one
chosen orbit coordinate is free.  Thus every signed coinvariant module has
a canonical decomposition into free orbit coordinates and one `C_2` for
each nonorientable orbit.  Write `T_J(X)` for the latter direct sum.

## The finite subgroup lemma

Use the actual cellular inclusion `H=D_8<K=S_4` and the restrictions of the
cellular orientation characters.

**Lemma 1.**  For every subgroup `L<K`:

1. `chi_K|_L` is nontrivial if and only if the restricted `H`-set `K/L`
   has a nonorientable orbit;
2. in that case, `K/L` has exactly one nonorientable `H`-orbit; and
3. the three-term cellular transfer has odd multiplicity on precisely that
   orbit and even multiplicity on every other `H`-orbit.

**Proof.**  This is a fixed finite calculation in `S_4`, independent of the
coefficient set or the projective prime.  There are eleven conjugacy classes
and thirty actual subgroups of `K`.  The classes, number of placements, and
whether their orientation restriction is nontrivial are:

| subgroup type | placements | nonorientable |
| --- | ---: | :---: |
| `1` | 1 | no |
| `C_2` inside `A_4` | 3 | no |
| odd `C_2` | 6 | yes |
| `C_3` | 4 | no |
| normal `C_2 x C_2` | 1 | no |
| nonnormal `C_2 x C_2` | 3 | yes |
| `C_4` | 3 | yes |
| `S_3` | 4 | yes |
| `D_8` | 3 | yes |
| `A_4` | 1 | no |
| `S_4` | 1 | yes |

For each of the thirty placements, partition the right cosets `L\K` into
right `H`-orbits.  Test the orientation character on the stabilizer of one
coset in each orbit.  In each of the twenty nonorientable cases there is
exactly one negative `H`-orbit.  Finally apply the three fixed boundary
representatives to the base coset: their multiplicities are odd exactly on
that orbit.  The remaining ten cases have no negative orbit.  This exhausts
all subgroups and proves the lemma.  The exact audit is
`experiments/sl3_projective_primary_transfer_audit.g`; it terminates with

`subgroups_checked=30 torsion_subgroups=20 unique_primary_transfer=true`.

The committed stdout certificate is
`experiments/sl3-projective-primary-transfer-audit.txt`.

End proof.

## Uniform splitting theorem

**Theorem 2.**  For every finite `K`-set `X`, the restriction of the first
degree-two cellular boundary to orientation torsion is the isomorphism
`(PTS1)`.  In orbit coordinates its matrix has one unit in every row and
column.

**Proof.**  Decompose `X` into transitive `K`-orbits.  By `(PTS3)`, a source
orbit contributes a `C_2` precisely when its stabilizer has nontrivial
orientation.  Lemma 1 says that its restriction contributes exactly one
target `C_2`, and that the transfer is nonzero on this coordinate.  A
nonzero homomorphism `C_2->C_2` is the identity.  Different `K`-orbits are
disjoint, so the direct sum is a permutation isomorphism.  End proof.

The statement holds for every finite coefficient action, not merely for
projective planes.  The two explicit cuspidal charts give a direct
coordinate check:

| level | `T_1` | torsion in first `2`-cell | unit rows covering `T_1` |
| ---: | ---: | ---: | ---: |
| `53` | 29 | 29 | 29 |
| `61` | 33 | 33 | 33 |

At level `53`, the full omitted torsion dimensions in degrees `1,2,3` are

`29, 84=29+55, 29`;

at level `61` they are

`33, 96=33+63, 33`.                                          `(PTS4)`

Theorem 2 cancels the first summand in the middle of `(PTS4)` against
degree one with norm one in the ordinary signed-coinvariant row.  Standard
algebraic chain cancellation modifies the adjacent maps in that row only by
composing with this permutation inverse.  Since the original boundary has
fixed incidence width, the modified zero-row maps retain a
chart-independent Schur norm.

## Consequence for TRUE

`TRUE_TWO_PRIMARY_CELLULAR_DERIVED_AUDIT.md` proves that the ordinary signed
orbit complex is not the missing free integral model: positive
stabilizer-homology rows are essential.  The present theorem removes one
entire interface from its zero-th row uniformly and exactly.  The residual
zero-row gate is narrower:

`second degree-two C_2 sector <-- degree-three C_2 sector`,     `(PTS5)`

together with its coupling to the free cuspidal lattice.  Unlike the
cancelled block, `(PTS5)` has genuine residual homology and is not claimed
to be contractible.  Moreover, the positive rows in HAP's existing derived
total complex must still be controlled.  A full TRUE proof therefore needs
a uniformly bounded decoder through the residual filtered augmentation, not
merely the norm-one cancellation proved here.  See
`TRUE_HAP_DERIVED_TOTAL_AUDIT.md` for that exact remaining map.
