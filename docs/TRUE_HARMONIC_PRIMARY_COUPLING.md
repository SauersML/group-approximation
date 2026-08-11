# Cuspidal harmonic classes cross the projective primary filtration

Date: 2026-08-11

## Outcome

The two certified compact cuspidal harmonic generators at levels `53` and
`61` have now been lifted through the full filtered HAP complex modulo two.
At both levels the rational signed-coinvariant model initially hides one
rank-one orientation-primary transgression.  Restoring the omitted
orientation-torsion coordinates in the two cellular degree-two blocks
removes it, and both harmonic generators then admit exact total HAP cycle
lifts.

Thus the actual cuspidal harmonic plane does **not** encounter a mod-two
existence obstruction at either of the first two cuspidal levels.  This is
the first direct computation of the coupling which remained open after the
derived-primary audit.

It is not yet a uniform integral decoder theorem.  The lifts are arbitrary
row-echelon solutions over `F_2`; their support is neither minimal nor a
canonical invariant, and no integral norm bound follows from two levels.

## 1. Exact zero-row identification

Let `N=p^2+p+1`.  HAP's total degree-two module has ten coefficient blocks,
with the last two blocks equal to the cellular bidegree `(2,0)`.  The compact
signed cellular degree-two module is obtained from those blocks by signed
stabilizer coinvariants.

The audit chooses one coefficient point in every free signed orbit and
forms the induced map from the last two HAP blocks to the compact
degree-one module.  For both `p=53` and `p=61`, the difference from the
previously certified compact cellular boundary has exact rank zero:

`HAP generators (8,9) -> compact cellular boundary`,
`rank(difference)=0`.                                      `(HPC1)`

Here generator indices are zero based.  Equation `(HPC1)` removes any
ambiguity from orbit ordering, cellular cell ordering, or coefficient-action
conventions.

## 2. Why the naive lift first fails

Over the integers, a signed orbit containing an orientation-reversing
stabilizer contributes a `C_2` torsion coinvariant.  The rational compact
complex deletes this orbit.  Reducing the already-rationalized compact
complex modulo two therefore does **not** recover the full mod-two
coinvariants: the deleted orientation orbits reappear.

At level `53`, the vertical edge block has rank `2470` inside `2863`
coordinates, so its full mod-two `H_0` has dimension

`2863-2470=393`.                                        `(HPC2)`

The free rational signed-coinvariant edge module has dimension `364`.
Their difference is exactly `29`, the number of omitted orientation-torsion
orbits.  Consequently a compact cycle can have zero compact cellular
boundary while its canonical representative still has a nonzero class in
the larger mod-two edge coinvariants.

For the two level-53 harmonic basis vectors, adjoining either syndrome to
the vertical edge boundary raises rank from `2470` to `2471`.  Both
syndromes are nonzero, but adjoining them simultaneously still raises rank
by only one.  Hence the induced map on the two-dimensional harmonic plane
has rank

`rank(transgression_53)=1`.                              `(HPC3)`

At level `61`, the vertical rank is `3270`.  One chosen harmonic basis
vector has zero syndrome class and the other raises the rank to `3271`, so

`rank(transgression_61)=1`.                              `(HPC4)`

The distinction between the individual basis vectors is basis dependent;
the rank-one statement is invariant.

## 3. Restoring the missing primary coordinates

The two cellular degree-two blocks have the following numbers of signed
orientation-torsion orbits:

| `p` | first two-cell block | second two-cell block |
| ---: | ---: | ---: |
| 53 | 29 | 55 |
| 61 | 33 | 63 |

These values agree with

`((p+5)/2, p+2)`                                           `(HPC5)`

at both levels.  This formula is an observed exact pattern, not yet a
proved all-prime theorem.

Allow one representative in every orbit from `(HPC5)`, together with the
`(1,1)` and `(0,2)` HAP correction blocks.  Exact sparse `F_2` elimination
then produces total degree-two cycles mapping to each compact harmonic
generator:

| `p` | basis | compact support | torsion correction | `(1,1)` correction | `(0,2)` correction | total support |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 53 | 0 | 149 | 39 | 1934 | 1809 | 3931 |
| 53 | 1 | 152 | 39 | 1925 | 1872 | 3988 |
| 61 | 0 | 224 | 46 | 2477 | 2580 | 5327 |
| 61 | 1 | 214 | 50 | 2569 | 2512 | 5345 |

Every displayed lift has exactly zero total boundary.  The total support
fractions are approximately `0.1373,0.1393,0.1408,0.1413` in the respective
`10N`-coordinate total modules.  Their stability is useful evidence for a
bounded local section, but support of one echelon solution is not an
operator-norm certificate.

The solver happened to choose all four lifts with coefficient zero on the
exceptional and first ordinary singleton representatives in the first
`(0,2)` generator.  Those coordinate values change when a total cycle is
modified by boundaries or lower-filtration cycles, so they do not prove
that the harmonic plane avoids the singleton decoder obstruction in an
invariant sense.

## 4. What is proved and what remains

The computation proves:

1. the compact-to-HAP zero-row identification is exact;
2. the two-dimensional cuspidal plane has a rank-one mod-two orientation
   transgression at both first cuspidal levels;
3. the transgression is canceled after the omitted two-cell orientation
   sectors are restored;
4. every certified compact harmonic generator at `p=53,61` lifts to a full
   mod-two HAP cycle.

It does not prove:

1. a uniformly bounded integral section;
2. that the displayed support pattern persists for every prime;
3. that the integral paired-discriminant carries avoid the distant
   singleton differences from
   `TRUE_BOUNDED_DEGREE_PARITY_DECODER_NO_GO.md`.

The next theorem-shaped target is to express `(HPC3)--(HPC5)` in the same
projective orbit coordinates used for the primary matching theorem.  An
all-prime rank-one transgression formula plus a fixed local torsion
cancellation would remove the **existence** part of the harmonic-primary
coupling uniformly.  The remaining quantitative problem would then be the
norm of the induced integral section on the paired harmonic carry lattice,
not a decoder on all primary boundaries.

## Reproducibility

The exact analyzer is
`experiments/sl3_projective_harmonic_primary_coupling.py`.  Its committed
certificates are

* `experiments/projective-harmonic-primary-p53-f2.json`, SHA-256
  `a33b2c9c4ce08f3cd1b8b868aca2fd2c623deccefe96795ed871a687dda280bc`;
* `experiments/projective-harmonic-primary-p61-f2.json`, SHA-256
  `17fc91d671dc9dae5bc48bd559b2c62190dfed0648f6560063abcd363aae0f2c`.

The raw full HAP boundaries are generated by
`experiments/sl3_projective_h2_export.g`; the compact signed cellular
exports and harmonic bases are the same exact inputs used in
`TRUE_P53_CELLULAR_HARMONIC_DISCRIMINANT.md` and
`TRUE_P61_CELLULAR_HARMONIC_SECTION.md`.
