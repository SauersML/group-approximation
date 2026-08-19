# An exact group-ring Hodge gap for `SL_3(Z)`

Date: 2026-08-11

## Result

Let `Gamma=SL_3(Z)` use the six elementary transvections and the thirteen
relators in `experiments/sl3_degree_one_spectrum.py`: six Steinberg
commutators, six displayed commuting-root commutators, and

`(x_12 x_21^(-1) x_12)^4=1`.                         `(SHS1)`

For a unitary representation `pi:Gamma->U(H)`, let

`d0:H->H^6`, `d1:H^6->H^13`                           `(SHS2)`

be the presentation coboundaries, and put

`Delta_1=d1^*d1+d0d0^*`.                              `(SHS3)`

**Theorem (exact certified Hodge gap).**  For every unitary representation
`pi` and every `xi in H^6`,

`<Delta_1 xi,xi> >= gamma ||xi||^2`,                  `(SHS4)`

where the exact rational constant is

`gamma = 14164556740143 / 5000000000000000`
`      = 0.0028329113480286`.                         `(SHS5)`

This makes the qualitative property-`(T)` gap in
`TRUE_PROPERTY_T_LINEAR_COCYCLE_GAP.md` explicit.  It is a universal
group-ring inequality, not an extrapolation from the finite-prime spectra.

## Exact certificate

Write `Delta` for `(SHS3)` as a `6 x 6` matrix over
`R[SL_3(Z)]`.  Group elements are stored canonically as their integral
`3 x 3` matrices.  Let `E` be the 22-element support consisting of the
relator prefixes needed for `d1`, together with the inverse-generator
support needed for `d0d0^*`.  Let `V` be the 132-entry group-ring monomial
row indexed by

`{1,...,6} x E`.                                      `(SHS6)`

The file `experiments/sl3-sos-radius0-certificate.npz` contains an integer
matrix

`Q_Z in M_(102 x 132)(Z)`, `Q=10^(-8) Q_Z`.           `(SHS7)`

Thus

`S=V^* Q^T Q V`                                      `(SHS8)`

is positive in every unitary representation, with no numerical positivity
assumption.  Exact Python-integer coefficient arithmetic gives the
self-adjoint residual

`R=Delta-(1/250)I-S`.                                 `(SHS9)`

For each matrix row `i`, the verifier computes

`rho_i=sum_(j,g)|coefficient_g(R_ij)|`.               `(SHS10)`

With common denominator `10^16`, the six exact numerators are

```text
11670886519714
11659124680677
11665866556524
11658749718021
11658998556031
11658961981218
```

Therefore

`rho=max_i rho_i=11670886519714/10^16`.               `(SHS11)`

For every unitary representation, each represented group element has norm
one.  The block row-sum bound and self-adjointness give

`||pi(R)|| <= rho`.                                   `(SHS12)`

Equations `(SHS8)--(SHS12)` prove

`Delta_1 >= (1/250-rho)I`
`        = 28329113480286/10^16 I`
`        = gamma I`,                                  `(SHS13)`

which is `(SHS4)`.

The certificate contains its 22 exact group matrices as well as `Q_Z`.
Its SHA-256 digest is

```text
5b83dc59e55b89a8f48e115e06ce72deaac2bccd5c3f1ded1ead3837c26b021b
```

## Independent checks

`experiments/sl3_group_ring_sos.py` constructs `Delta` directly from the
presentation words.  Evaluation on the independently constructed finite
Schreier complexes has exactly zero differing sparse entries at both `p=3`
and `p=5`.

The discovery SDP used a 132-dimensional positive-semidefinite Gram
variable.  It found the larger floating candidate

`c_SDP=0.005161566104540423`                           `(SHS14)`

with maximum coefficient violation `3.78e-8`.  The proof does not trust
that positivity or feasibility: negative numerical eigendirections were
discarded, the retained factor was rounded to `(SHS7)`, and the entire loss
from rounding and coefficient mismatch is paid explicitly by `(SHS11)`.

Cold verification requires NumPy/SciPy but not CVXPY, SCS, or the original
floating Gram matrix:

```text
python experiments/sl3_sos_certificate.py \
  --certificate experiments/sl3-sos-radius0-certificate.npz --verify
```

It reconstructs the presentation, checks that the stored support agrees,
forms `Q_Z^T Q_Z` with arbitrary-precision Python integers, checks the
residual is self-adjoint, and prints `"valid": true` only when the exact
numerator in `(SHS13)` is positive.

## Explicit robust real cocycle repair

By property `(T)`, `Z^1(Gamma,pi)=im(d0)` is closed.  For any
`a in H^6`, decompose it orthogonally as

`a=a_Z+a_perp`, `a_Z in Z^1`, `a_perp perpendicular Z^1`. `(SHS15)`

Then `d0^*a_perp=0` and `d1a_perp=d1a`.  Equation `(SHS4)` gives

`||a_perp|| <= gamma^(-1/2)||d1a||`
`             <18.789 ||d1a||`.                      `(SHS16)`

Hence

`dist(a,Z^1(Gamma,pi)) <18.789 ||d1a||`.              `(SHS17)`

This is the explicit version of `(PTG4)` in
`TRUE_PROPERTY_T_LINEAR_COCYCLE_GAP.md` for the chosen presentation.

## Consequence for the main problem

This closes the real-linear spectral subproblem that motivated
`experiments/sl3_degree_one_spectrum.py`: the observed finite-chart gap is a
shadow of a universal group-ring gap, and all scalar-character blocks are
controlled simultaneously.

It does **not** prove that every hyperlinear group is sofic.  Circle-valued
phase repair still has integer carries and finite-order/Hamming constraints
which are invisible to the real Hilbert-space inequality `(SHS17)`.  It also
does not construct the nonliftable projective sector required for FALSE.
The next proof-search target is now narrower: determine whether the exact
circle curvature can be lifted so that `(SHS17)` applies without losing its
torsion class, or prove an integral obstruction to that lift.
