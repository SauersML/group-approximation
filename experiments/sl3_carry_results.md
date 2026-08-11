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
`docs/TRUE_INTEGRAL_CARRY_TRANSVERSALITY.md` closes the proposed search for
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

`docs/INTEGRAL_CARRY_DISCRIMINANT_DUALITY.md` identifies the exact next
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
