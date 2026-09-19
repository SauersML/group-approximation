# Integral carry search on the exact `SL_3(Z)` charts

Date: 2026-08-11

## Scope

For the finite exact action on `X_p=F_p^3-{0}`, put

`A_p=d1:Z^edges -> Z^cells`.

The real SOS theorem controls the least positive singular value of `A_p`.
The remaining circle problem is the lattice transversality constant

`Theta(A_p)=sup_(z notin L_p) dist(z,L_p)/dist(z,ran_R A_p)`,

where

`L_p=ran_R(A_p) intersect Z^cells`.

The experiments here search for lower-bound witnesses and audit the
saturation quotient `L_p/A_p(Z^edges)`.  They do not compute `Theta(A_p)`
exactly.

All runs used at most four cores on one shared compute node.  Dense QR was
stopped at `p=7`; larger leverage values use sparse LSMR.  The dense `p=5` Smith form
was terminated when it exceeded the useful iteration budget and was
replaced by modular ranks and exact maximal-minor certificates.  No process
or job remains.

## The universal generalized inverse is impossible

Before computation, Proposition 4 of
`notes/TRUE_INTEGRAL_CARRY_TRANSVERSALITY.md` closes the proposed search for
one `B` over `Z[G]` satisfying `DBD=D`.  For an infinite one-ended group,
`H^1(G,Z[G])=0` identifies `ker D` with `im d0`.  An inner inverse would
split that image, while augmentation forbids a left inverse to the column
of `s-1` terms.  Since `SL_3(Z)` is one-ended, no amount of group-ring
support expansion can find `(ICT40)`.

The surviving target is chart-dependent lattice geometry.

## Basis-carry leverage

For a cell coordinate `e_c`, let `h_c` be its row leverage in `A_p`.  Then

`dist(e_c,ran_R A_p)=sqrt(1-h_c)`.

If this distance is nonzero, integrality gives
`dist(e_c,L_p)>=1`, and hence

`Theta(A_p)>=1/sqrt(1-h_c)`.

Dense pivoted QR at `p=3,5,7` found that the best coordinate is always a
CRW torsion cell on the fixed projective axis.  Sparse LSMR then followed
the same coordinate through `p=37`:

| `p` | distance to real range | basis lower bound for `Theta` | LSMR iterations |
|---:|---:|---:|---:|
| 3  | 0.220260755643 | 4.540073410177 | 53 |
| 5  | 0.220122855661 | 4.542917622052 | 76 |
| 7  | 0.220113046221 | 4.543120079287 | 91 |
| 11 | 0.220114092466 | 4.543098484962 | 105 |
| 17 | 0.220114225932 | 4.543095730264 | 107 |
| 23 | 0.220114157542 | 4.543097141807 | 114 |
| 37 | 0.220114186340 | 4.543096547413 | 116 |

The normal-equation residual is below `1.6e-11` in every listed run.  This
witness stabilizes near `4.543096`; it does not grow with the chart.

The exhaustive two-cell search is weaker.  Its best lower bounds are
`3.21394` at `p=3` and `3.21346` at `p=5`.

## LLL searches

`sl3_carry_lll.py` embeds projected integer carries as

`z |-> (round(10^5 P_perp z),z)`

and reduces the resulting lattice with `fpylll`.

* On all torsion cells, at both `p=3` and `p=5`, LLL returns a single cell
  as the shortest nonexact projected vector.  No coordinated torsion-cell
  carry beats `4.543`.
* On all 338 cells at `p=3`, LLL again returns distance
  `0.220260755643`.  Its displayed large coefficient vector has the same
  projected norm as the one-cell class; numerically it differs by an
  attainable real-range vector rather than defining a shorter class.

These are heuristic shortest-vector searches, not upper-bound certificates
for `Theta`.

## Exact saturation arithmetic

`sl3_carry_smith.py` computes the exact Smith form at `p=3`:

`diag(1,...,1,3,0,...,0)`, with 130 unit factors.         `(SCA1)`

Thus

`L_3/A_3(Z^edges) ~= C_3`.                              `(SCA2)`

The chart-prime torsion pattern does not continue automatically.  At
`p=5`, exact modular ranks are full for every coefficient prime from `2`
through `97`.  More decisively,
`sl3_carry_minor_certificate.py` stores three exact `621 x 621` minors with
determinants

```text
-110090388146818391519484129787700025029397702906537984
2142487245
4883810560
```

Their gcd is exactly one.  Therefore the gcd of all maximal minors is one,
and

`L_5=A_5(Z^edges)`.                                    `(SCA3)`

This is a cold-verifiable exact certificate, not a modular inference:

```text
python experiments/sl3_carry_minor_certificate.py \
  --verify experiments/sl3-carry-minor-saturation-p5.jsonl
```

The verifier reconstructs the integer relator matrix, extracts the stored
row and column sets, recomputes all three determinants with FLINT, and checks
their gcd.

## Interpretation and next target

The first carry campaign found no divergent transversality witness.  The
strongest sparse, pair, torsion-lattice, and full-`p=3` lattice searches all
reduce to the same fixed-axis torsion-cell scale near `4.543`.  The exact
`p=5` certificate also removes hidden saturation torsion entirely on that
chart.

This is positive evidence for bounded `Theta(A_p)`, but it is not an upper
bound and therefore not the circle-repair theorem.  A bad carry could be a
long integer combination missed by LLL, and saturation alone gives no
Euclidean control on a lattice inverse.

`notes/INTEGRAL_CARRY_DISCRIMINANT_DUALITY.md` identifies the exact next
object.  Compute the primitive cycle lattice

`K_p=ker(d1^T) intersect Z^cells`

and the discriminant group of its Gram matrix.  `Theta(A_p)` is a finite
maximum of paired closest-vector radii over those discriminant classes.
This is different from the saturation quotient computed above.

The proof-producing successor should exploit chart symmetry to control all
of these discriminant classes uniformly, or produce a class whose dual
cycle representative tends to zero relative to its glued range radius.  The
fixed-axis and saturation data are calibration invariants for that solver.
Do not resume dense Smith forms of `d1`; use sparse modular selection and
exact determinant/gcd certificates, then move to the primitive cycle Gram
lattice which actually governs `Theta`.

## Exact primitive cycle discriminant at `p=3`

`sl3_carry_cycle_discriminant.py` obtains a primitive basis from the zero
rows of a transformed row Hermite form.  It independently checks that every
Smith factor of the resulting `338 x 207` basis is one.  The cycle Gram
matrix has determinant

`111860100927858053679845003076090458883815688550015485832058016128295803340756802716303360`

and 13 nonunit Smith factors:

`3,3,6,6,6,6,6,6,18,18,108,648,`
`11748473010802458762353905411768954045704229041349662360748852518665758026240`.

Thus even the smallest chart has a 296-bit discriminant and cannot be
handled by enumerating discriminant classes.  The fixed-axis torsion cell
already has discriminant-class order

`489519708783435781764746058823706418571009543389569265031202188277739917760`,

while its exact squared carry ratio is only

`20396654532643157573531085784321100773792064307898719376300091178239163240`
`/989539625037043080774308299417824307996183859749981101022908782774423723`

`=20.612266569799...`.  Large class order therefore does not imply large
distortion.  Symmetry or a structural lattice inequality is mandatory.

The exact output is cold-replayed by

```text
python experiments/sl3_carry_cycle_discriminant.py \
  --verify experiments/sl3-carry-cycle-discriminant-p3.json
```

As a calibration of the constant-cycle theorem below, direct Hermite
arithmetic proves `S(K_3)=K_1`.  At `p=5`, the transform-free combined-map
certificate in `sl3_carry_transfer_certificate.py` has three
`628 x 628` minors with determinants

`-2142487245, 39070484480, -23842199808`.

Their gcd is one, so the combined `(d1^T,S)` image is saturated.  Constant
rational lifts then prove `S(K_5)=K_1` integrally.  Verify it with

```text
python experiments/sl3_carry_transfer_certificate.py \
  --verify experiments/sl3-carry-transfer-p5-certificate.json
```

## Scalar-involution gluing code

The scalar involution `x |-> -x` decomposes the rational cycle space into
plus and minus sectors, but the integral cycle lattice need not split.  Its
failure to split is the exact binary code obtained by recording, modulo
two, the sum of a cycle on each paired cell orbit.

At `p=3`, the plus and minus cycle ranks are `103` and `104`.  Their direct
sum has exact index

`2^103 = 10141204801825835211973625643008`

in the full primitive cycle lattice.  The corresponding gluing code is
`[169,103]`.  At `p=5` it is `[806,495]`.  Thus the scalar split removes the
odd-character coupling, but leaves a maximal-scale 2-primary gluing problem.

The code is sparse but not bounded-locally generated:

| `p` | weight-one words | rank generated through weight 4 | full rank |
|---:|---:|---:|---:|
| 3 | 16 | 61 | 103 |
| 5 | 44 | 157 | 495 |

A greedy basis selected from the natural mod-2 cycle basis has maximum
weights `28` and `141`, respectively.  Its weight quartiles are
`1,3,6,14,28` at `p=3` and `1,5,25,85,141` at `p=5`.  Therefore neither an
expanding-code picture nor generation by a fixed list of support-at-most-four
patterns describes this gluing.

These are exact finite-field and integer-lattice computations.  Replay them
with the installed SageMath stack:

```text
sage -python experiments/sl3_carry_gluing_code.py \
  --verify experiments/sl3-carry-gluing-code.jsonl
```

The live compression problem is now sharper: control the Euclidean cost of
the high-support binary gluing sectors, not merely their dimension, class
order, or minimum weight.  A useful successor should combine the scalar
character blocks with the exact gluing code rather than optimize the full
296-bit discriminant module blindly.

## The constant-cycle transfer route is closed

Sections 6--10 of
`notes/INTEGRAL_CARRY_DISCRIMINANT_DUALITY.md` give a low-dimensional test
for discriminant classes of the form

`u=Jv/m`, `v in ker(d1_1^T)`.                         `(SCA4)`

If `M_p` is the image of chart `2`-cycles under coordinate transfer, the
largest possible denominator is

`m_p(v)=gcd{<v,w>:w in M_p}`.                         `(SCA5)`

This initially looks like a useful fixed-rank modular search.  It is now
closed theoretically.  Every spherical presentation cycle lifts to every
cover and pushes back unchanged, so

`ker(d1_1^T)/M_p` is a quotient of
`H_2(SL_3(Z),Z) ~= C_2 directSum C_2`.                `(SCA6)`

Consequently, with

`g(v)=gcd{<v,w>:w in ker(d1_1^T)}`,

one has the uniform bound

`m_p(v) divides 2g(v)`.                               `(SCA7)`

Thus no constant base cycle can produce a denominator growing with
`|X_p|`.  The exact `p=5` saturation certificate makes the annihilator and
modular-column-space versions of this test equivalent, but the
Schur-multiplier theorem already bounds both on every chart.

Do not launch the proposed constant-lift modular membership sweep.  Any bad
carry must lie in a genuinely new-cover discriminant class of `K_p`, not in
the transfer sector generated from `ker(d1_1^T)`.  The full cycle Gram
module remains the live object.
