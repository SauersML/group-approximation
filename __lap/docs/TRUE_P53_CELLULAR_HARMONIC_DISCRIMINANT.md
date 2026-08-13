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

## The shortest class has exact integral lift energy four

The short class now has a complete paired metric certificate.

Let `u` be its shortest representative.  Any ambient integral lift has the
orthogonal form

`z=u+b`, `z in Z^328`, `b in ran_R(d2^T)`.                    `(PCH12)`

Because the class is nonzero, `z` is nonzero, and hence

`||z||^2 in Z_(>0)`.                                        `(PCH13)`

The Pythagorean lift formula therefore gives

`lambda(u)^2=||u||^2+rho_L(eta(u))^2>=1`,                   `(PCH14)`

but integrality gives much more here.  Exact BKZ/Babai reduction in the
saturated range lattice produces the four-term lift

`z=e_240-e_287-e_302+e_304`,                               `(PCH15)`

using zero-based cellular coordinates.  It satisfies the degree-three
cocycle equations and all `104` required integral cycle pairings exactly,
so `lambda(u)^2<=4`.

The reverse inequality has a small exhaustive certificate.  An integral
vector of squared norm below four is a signed sum of at most three distinct
coordinate vectors.  The cycle-pairing profile of such a vector is a signed
sum of at most three of the `328` columns of the cycle basis.  The verifier
checks all `656` signed singletons and all

`4 binom(328,2)=214512`                                    `(PCH16)`

signed pairs.  The target is neither a singleton nor a pair, and no
target-minus-singleton profile is a pair on two distinct remaining
coordinates.  Therefore no lift of squared norm zero, one, two, or three
exists.  Consequently

`lambda(u)^2=4`,
`rho_L(eta(u))^2=4-a/q`,                                  `(PCH17)`

and this class contributes the exact paired distortion

`lambda(u)/||u||=2sqrt(q/a)`
` =7.489055360091924...`.                                  `(PCH18)`

In particular,

`kappa_Sigma^2>=4q/a=56.08595018652158...`.                 `(PCH19)`

This is the exact numerator compensation behind the coarse inequality
`Theta>=1/delta_H` in `TRUE_PROJECTIVE_HARMONIC_SYSTOLE.md`.

The original HNF lift had squared norm
`35939851216607643678587654132133`; this discrepancy was entirely a bad
choice of affine representative.  The exact certificate is
`experiments/projective-cellular-p53-cvp-exact.json`, its four-term lift is
`experiments/projective-cellular-p53-cvp-exact.tsv`, and the reproducible
verifier is `experiments/sl3_projective_cellular_cvp.py`.

## A near-optimal full rank-two integral section

The second Gauss-reduced basis vector also has a small verified integral
lift.  A short LLL/BKZ continuation gives

`z_2=e_45+e_49+e_52+e_55+e_107-e_178+e_219-e_242`
`    +e_247-e_262-e_283+e_298-e_303-e_308+e_316+e_325`, `(PCH20)`

again in zero-based coordinates.  Its squared norm is `16`.  Exact cycle
pairings and the degree-three cocycle equations verify that it lifts the
second reduced basis vector.  No optimality assertion for `z_2` is needed.
Its support is disjoint from `(PCH15)`, so the two lift vectors have Gram
matrix

`G_Z=[[4,0],[0,16]].`                                      `(PCH21)`

In the same basis, write

`G_H=(1/q)[[a,b],[b,c]]`,                                  `(PCH22)`

where `a` is `(PCH8)` and

`b=-56747109056607762375194153269785554845473318947639702446220798724932267608137725`,

`c=13652477141855668986785589318594066780128481258677480963257028544207685068564640667`.

The squared singular values of the resulting integral section are the two
roots of the exact generalized characteristic polynomial

`det(G_Z-lambda G_H)`
` =(D/q)lambda^2-(E/q)lambda+64`,                           `(PCH23)`

with

`D=973496034304122008340916042563771299469198884174733931892389656553715746971291164`,

`E=74315925848129849388919270039641281094704409235664714312287796710826788318362054876`.

They are approximately

`20.236460080505854`, `56.10275777902312`.                 `(PCH24)`

Consequently the section norm is

`||s||=7.49017741972933...`.                               `(PCH25)`

Combining `(PCH18)` with the general inequality
`kappa_Sigma<=||s||` gives the rigorous compact-model bracket

`7.489055360091924...`
` <=kappa_Sigma<=7.49017741972933...`.                     `(PCH26)`

Thus the full free rank-two harmonic lift problem at level `53` is bounded
to a relative interval of about `1.5*10^(-4)`.  The enormous HNF section
norm `3.649*10^29` was entirely basis pathology, not an intrinsic
high-order discriminant obstruction.

The second lift and its modular lower-bound audit are in
`experiments/projective-cellular-p53-cvp-basis1-certified.json` and its TSV
companion.  The combined exact polynomial certificate is
`experiments/projective-cellular-p53-section.json`, produced by
`experiments/sl3_projective_cellular_section.py`.

## Two essential scope qualifications

The phrase "exact integral" in this note refers to the free coordinate
lattice of the rational signed-coinvariant complex.  Two issues must be
kept separate.

First, an orientation-reversing stabilizer relation `e=-e` creates a
`Z/2` coinvariant, while the rational signed quotient kills that coordinate.
There are `84` such degree-two coordinates at `p=53`.  The computation
therefore determines the free rational lattice exactly but does not determine
the full two-primary integral cellular complex.  The naive unsigned mod-two
orbit complex is insufficient; positive stabilizer-homology rows are forced.
This derived bounded-primary correction is isolated in
`TRUE_TWO_PRIMARY_CELLULAR_DERIVED_AUDIT.md` and
`TRUE_FIXED_RESOLUTION_DECODER_INVARIANCE.md`.

Second, the standard Euclidean metric on the `328` orbit coordinates is the
compact model's metric.  It is not literally the normalized coordinate
metric in the free HAP Shapiro resolution or in the original projective
carry chart.  A bounded chain comparison transports decoder bounds between
the models, but its norm must be included.  Thus the huge order `q` is not,
by itself, a FALSE certificate for the original carry problem.

These qualifications do not affect `(PCH1)--(PCH26)` as statements about
the displayed compact free lattice.  They delimit the remaining transfer
theorem needed to use the certificate in the universal problem.

## Consequences for the open problem

This calculation rules out two previously plausible shortcuts.

* Nonzero cuspidal homology is not merely an abstract location for a
  possible obstruction: in the compact `p=53` model it contains a concrete
  nonintegral sub-threshold class.
* The order of the harmonic discriminant can be enormous even though the
  harmonic rank is only two, while the full rank-two integral section can
  nevertheless have norm below `7.491`.  Discriminant order is not a proxy
  for repair cost, and a proof cannot enumerate discriminant classes.

It does not decide TRUE or FALSE.  The next exact tasks are:

1. retain the two-primary stabilizer coordinates, or prove a uniform
   bounded correction after inverting the fixed stabilizer orders;
2. construct the explicit bounded chain comparison to the free HAP carry
   complex;
3. repeat the same compact invariant and section construction at later
   cuspidal primes and determine
   whether the transferred dual systole tends to zero or stays uniformly
   bounded below.

If the transferred systole tends to zero, the integral-energy quantization
forces carry distortion to diverge.  If a uniformly bounded section can be
constructed, the harmonic layer of the TRUE decoder is solved.  The
remaining universal chart-selection quantifier is separate in either case.
