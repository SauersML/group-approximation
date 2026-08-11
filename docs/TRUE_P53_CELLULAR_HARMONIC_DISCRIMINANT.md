# The compact level-53 cellular model has an exact cyclic harmonic discriminant

Date: 2026-08-11

## Outcome

The non-free HAP complex `ContractibleGcomplex("SL(3,Z)")`, tensored with
the level-`53` projective permutation module and reduced by signed cell
stabilizer coinvariants, gives the exact rational complex

`Q^141 <- Q^364 <- Q^328 <- Q^112`.                         `(PCH1)`

Its boundary ranks are

`rank(d1)=140`, `rank(d2)=224`, `rank(d3)=102`,              `(PCH2)`

both consecutive products vanish, and therefore

`dim_Q H_2=328-224-102=2`.                                  `(PCH3)`

This independently reproduces the level-`53` cuspidal plane in a complex
which is two orders of magnitude smaller than the free HAP Shapiro complex.

More importantly, exact lattice arithmetic in the `328` free
signed-coinvariant coordinates determines the full harmonic discriminant.
With

`K=ker(d2^T) intersect Z^328`,
`H=ker(d2^T) intersect ker(d3)`,
`K_H=K intersect H`,
`Q^#=K^# intersect H`,                                      `(PCH4)`

one has `rank(K)=104`, `dim(H)=2`, and

`Q^#/K_H ~= Z/qZ`,                                          `(PCH5)`

where

`q=17269229743444936295695902979877937666574454551881432366677092780148396252626561139`.
                                                                  `(PCH6)`

Thus the compact model contains a nonzero harmonic discriminant class of
full order `q`.  A Gauss-reduced basis of `Q^#` proves that the shortest
nonintegral class has squared norm

`r=a/q`,                                                     `(PCH7)`

where

`a=1231626080044198340111057047829063373386905262559674403703730158374753002756468263`.
                                                                  `(PCH8)`

Numerically,

`r=0.07131910909412156...`,
`sqrt(r)=0.26705637811915589...`.                            `(PCH9)`

The largest squared norm of a degree-three boundary template in these
coordinates is `12`, and the exact inequality

`12a<q`                                                      `(PCH10)`

puts this class strictly below the spherical localization threshold
`1/sqrt(12)`.

This is the first exact non-acyclic compact-chart discriminant certificate.
It is stronger than the previous statement `dim_Q H_2=2`: it proves that
the harmonic plane really contains a nonintegral dual point and computes
its exact shortest norm and order.

## Exact construction

The GAP exporter `experiments/sl3_projective_cellular_export.g` records:

1. every finite cell stabilizer and its orientation sign;
2. its permutation on `P^2(F_53)` in the symmetric-square realization;
3. every cellular boundary term and its coefficient permutation.

The Sage program `experiments/sl3_projective_cellular_analyze.py` forms the
signed coinvariants, combines duplicate entries, and checks `d^2=0`.  It
then computes saturated integer kernels in the free coinvariant coordinates.

If the rows of `B_H` are an integral basis of `K_H` and the rows of `B_K`
are an integral basis of `K`, the lattice of all integral pairing columns

`{B_H k^T:k in K}`                                          `(PCH11)`

is a rank-two sublattice of `Z^2`.  Taking its Euclidean dual and applying
the same basis to `B_H` gives `Q^#`.  Smith reduction of
`K_H subset Q^#` gives the invariant factors `[1,q]` in `(PCH5)`.  Binary
Gauss reduction is exact, so the first diagonal entry of the reduced Gram
matrix is the genuine first minimum `(PCH7)`, not an LLL heuristic.

The hash-bearing certificate is
`experiments/projective-cellular-p53-summary.json`.  The two integral
harmonic vectors and the `Q^#` basis with integral ambient lifts are in

* `experiments/projective-cellular-p53-harmonic.tsv`;
* `experiments/projective-cellular-p53-qsharp-lifts.tsv`.

The summary verifies their residuals and records SHA-256 hashes of both
files.

## A rigorous paired-lift lower bound

The short class already yields a nontrivial metric certificate without
solving a `224`-dimensional closest-vector problem.

Let `u` be its shortest representative.  Any ambient integral lift has the
orthogonal form

`z=u+b`, `z in Z^328`, `b in ran_R(d2^T)`.                    `(PCH12)`

Because the class is nonzero, `z` is nonzero, and hence

`||z||^2 in Z_(>0)`.                                        `(PCH13)`

The Pythagorean lift formula therefore gives

`lambda(u)^2=||u||^2+rho_L(eta(u))^2>=1`,                   `(PCH14)`

so

`rho_L(eta(u))^2>=1-a/q`,
`lambda(u)/||u||>=sqrt(q/a)`
` =3.744527680045962...`.                                   `(PCH15)`

Equivalently, the compact model's harmonic integral-lift distortion obeys

`kappa_Sigma^2>=q/a=14.02148754663039...`.                  `(PCH16)`

This is the exact numerator compensation behind the coarse inequality
`Theta>=1/delta_H` in `TRUE_PROJECTIVE_HARMONIC_SYSTOLE.md`.

The exported HNF lift has squared norm

`35939851216607643678587654132133`,                          `(PCH17)`

and hence gives only the enormous upper bound
`2.2448...*10^16` on the same distortion.  It is a deliberately crude
right inverse.  Neither `(PCH17)` nor the still larger raw section norm is
evidence that the optimal decoder is large; only the lower bound `(PCH16)`
is presently intrinsic.

## Two essential scope qualifications

The phrase "exact integral" in this note refers to the free coordinate
lattice of the rational signed-coinvariant complex.  Two issues must be
kept separate.

First, an orientation-reversing stabilizer relation `e=-e` creates a
`Z/2` coinvariant, while the rational signed quotient kills that coordinate.
The computation therefore determines the free rational lattice exactly but
does not determine the full two-primary integral cellular complex.  This is
precisely the bounded-primary correction isolated in
`TRUE_FIXED_RESOLUTION_DECODER_INVARIANCE.md`.

Second, the standard Euclidean metric on the `328` orbit coordinates is the
compact model's metric.  It is not literally the normalized coordinate
metric in the free HAP Shapiro resolution or in the original projective
carry chart.  A bounded chain comparison transports decoder bounds between
the models, but its norm must be included.  Thus the huge order `q` is not,
by itself, a FALSE certificate for the original carry problem.

These qualifications do not affect `(PCH1)--(PCH16)` as statements about
the displayed compact free lattice.  They delimit the remaining transfer
theorem needed to use the certificate in the universal problem.

## Consequences for the open problem

This calculation rules out two previously plausible shortcuts.

* Nonzero cuspidal homology is not merely an abstract location for a
  possible obstruction: in the compact `p=53` model it contains a concrete
  nonintegral sub-threshold class.
* The order of the harmonic discriminant can be enormous even though the
  harmonic rank is only two.  A proof cannot enumerate discriminant classes.

It does not decide TRUE or FALSE.  The next exact tasks are:

1. retain the two-primary stabilizer coordinates, or prove a uniform
   bounded correction after inverting the fixed stabilizer orders;
2. construct the explicit bounded chain comparison to the free HAP carry
   complex;
3. find a genuinely short integral section for the rank-two lift sequence,
   or prove a basis-independent lower bound stronger than `(PCH16)`;
4. repeat the same compact invariant at later cuspidal primes and determine
   whether the transferred dual systole tends to zero or stays uniformly
   bounded below.

If the transferred systole tends to zero, the integral-energy quantization
forces carry distortion to diverge.  If a uniformly bounded section can be
constructed, the harmonic layer of the TRUE decoder is solved.  The
remaining universal chart-selection quantifier is separate in either case.
