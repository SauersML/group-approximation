# Admissible mixed surgery and an explicit operator-small Iwahori step

2026-09-08. Three finite-dimensional lemmas below construct admissible
operations and a conditional contracting step. No sixth-moment flatness
is assumed. The lemmas do not select the global surgery or prove that
every small-defect pair satisfies the spectral condition of Section 3.
Consequently they do not settle flexible Iwahori repair or nonhyperlinearity.

Use the exact modular parameterization from
[the modular chart proof](modular-vertex-admissible-charts-2026-09-08.md).
For one exact vertex write `S^2=B^3=Z`, with `Z^2=I`, and let

```text
Psi_rho(H)(s)=exp(H_0) exp(H_4) S exp(-H_4) exp(-H_0),
Psi_rho(H)(b)=exp(H_0) exp(H_6) B exp(-H_6) exp(-H_0).
```

The anti-Hermitian parameters satisfy `ZH_0Z=-H_0` and
`[H_4,Z]=[H_6,Z]=0`. For two vertices there are six parameters.
All matrix Schatten norms use normalized trace. Unless explicitly
specified otherwise, tuple norms are maxima over their entries.

## 1. Exact high/low splitting inside the admissible coordinates

Fix `theta>0`. Spectrally split every parameter into

```text
H_j=H_j^hi+H_j^lo,
H_j^lo=H_j 1_(|H_j|<=theta),
H_j^hi=H_j 1_(|H_j|>theta).                            (1)
```

These two pieces commute. They remain in the admissible parameter
space: central commutation is preserved by functional calculus, while
the cutoff function for `-iH_0` is odd, so both pieces still
anticommute with `Z`.

Put `rho^hi=Psi_rho(H^hi)` and `U_0=exp(H_0^hi)`. Its central
involution is `Z^hi=U_0 Z U_0^*`. Define new parameters at this
new exact vertex by

```text
K_j=U_0 H_j^lo U_0^*       (j=0,4,6).                  (2)
```

They obey the corresponding central conditions for `Z^hi`. Moreover,
direct multiplication, using commutation of each parameter's two
spectral pieces, gives the exact composition identity

```text
Psi_(rho^hi)(K)=Psi_rho(H).                            (3)
```

In particular, this is an admissible surgery followed by an admissible
operator-small step, with an exact vertex representation at the
intermediate point. It is not a splitting of ambient generator
increments which might violate the vertex relations.

Let `a=max_j ||H_j||_2` in dimension `n`. Spectral counting gives

```text
rank(H_j^hi)/n <= a^2/theta^2.                         (4)
```

The rank of `exp(H_j^hi)-I` is at most the rank of `H_j^hi`.
Telescoping the four exponential slots of each generator gives

```text
max_g rank(rho^hi(g)-rho(g))/n <= 4a^2/theta^2,
max_g ||rho^hi(g)-rho(g)||_2 <= 4a.                    (5)
```

The second inequality follows from `||exp(X)-I||_2<=||X||_2`
for anti-Hermitian `X`, and has no operator-norm smallness assumption.
Unitary conjugation in (2) preserves all Schatten norms, so

```text
||K||_op<=theta,       ||K||_2<=a,
max_g ||Psi_(rho^hi)(K)(g)-rho^hi(g)||_op <=4theta,
max_g ||Psi_(rho^hi)(K)(g)-rho^hi(g)||_2 <=4a.          (6)
```

The same bounds hold for both vertices together. Thus a supplied
parameter of HS size `O(sqrt(e))` splits, at any fixed positive
threshold, into rank `O(en)` surgery and a bounded-operator-norm
step, with HS cost `O(sqrt(e))` for both stages.

Every stage in (3) stays in the original torsion-multiplicity stratum.
This splitting does not change discrete vertex types, supply missing
dimensions, or construct a residual-canceling parameter in the first
place.

## 2. Extracting a selected central-positive block by paid rank surgery

There is also a simple operation not requiring a selected projection
to reduce the two vertex generators beforehand. For one vertex let
`P` be an orthogonal projection of rank `r` with `ZP=P`.
Form the two cyclic hulls

```text
E_S=span(Ran(P), S Ran(P)),
E_B=span(Ran(P), B Ran(P), B^2 Ran(P)).                 (7)
```

They lie in the positive central sector. Since `S^2=I` and
`B^3=I` there, they reduce `S` and `B`, respectively, with
dimensions at most `2r` and `3r`. Replace `S` by the identity on
`E_S`, retaining it on `E_S^perp`; independently replace `B` by
the identity on `E_B`, retaining it on `E_B^perp`. Call the results
`S',B'`. Then

```text
(S')^2=(B')^3=Z,
rank(S'-S)<=2r,        rank(B'-B)<=3r,
S'P=B'P=P.                                            (8)
```

Thus the output is an exact vertex representation and `P` is now a
trivial reducing block. If the two vertices have a common central
involution and `P` lies in its positive sector, apply this operation
to both vertices. The selected block is then exactly compatible,
and the maximum normalized-HS generator cost is at most
`2 sqrt(3r/n)`.

The operation uses separate finite cyclic hulls. It does not assume
that the original pair has a common reducing subspace containing `P`,
which would exclude irreducible input vertices. On the other hand,
it can create new mismatch on the parts of those hulls outside `P`.
For a residual which is a difference of two words of length at most
`ell`, the rank of its change is at most `6 ell r`, by telescoping.
That rank estimate supplies no decrease of the residual norm.

Equation (8) is restricted to the positive common central sector.
It is not a claim that an arbitrary negative-central block can be
replaced by compatible one-dimensional characters.

## 3. A finite-polynomial correction with a dimension-free contraction

This section uses Hilbert tuple norms: the square root of the sum of
the squared normalized-HS norms of the entries. The operator tuple norm
remains the maximum. There are six parameter entries and three Iwahori
residual entries, so conversion to the maximum HS convention costs only
fixed numerical constants.

At any pair `q` of exact modular vertex representations, let

```text
F(X)=Iwahori residual of Psi_q(X),
f=F(0),       e=||f||_2,       delta=||f||_op,
L=DF(0).                                               (9)
```

The parameter domain is the real Hilbert space of admissible
anti-Hermitian tuples. Let `L*` be its real HS adjoint. If the two
words defining each residual coordinate have lengths at most `ell`,
there is a constant `C>=1`, depending only on `ell`, such that

```text
||L||_(2->2) <= C,
||L||_(op->op) <= C,      ||L*||_(op->op) <= C,
||D^2F(X)[A,B]||_2 <= C ||A||_op ||B||_2              (10)
```

at every parameter base point `X` for the last estimate. One may
take a coarse common constant `C=100 ell^2` for these three residual
coordinates.

Here the mixed Hessian estimate is the proved word derivative bound.
For the adjoint assertion, differentiate each exponential slot at zero.
Each residual row is a sum of at most `8 ell` signed unitary
left/right multiplications of parameter entries. The adjoint reverses
those multiplications and then projects onto the admissible parameter
space. Anti-Hermitian projection and the maps
`X -> (X+ZXZ)/2`, `X -> (X-ZXZ)/2` are operator-norm contractions.
Summing over three residual entries therefore bounds `L*` in
operator norm by `24 ell`. The HS operator bound follows from the
same finite sum, or its Hilbert adjoint. This proves (10) without
assuming an operator-norm estimate for a Moore--Penrose inverse.

Fix a spectral threshold `0<sigma<=C`. Suppose

```text
||1_([0,sigma^2))(L L*) f||_2 <= e/8.                 (11)
```

This projection includes the kernel; no surjectivity of `L` is
assumed. Choose an integer `T>=1`, depending only on `sigma,C`,
such that

```text
(1-sigma^2/C^2)^T <= 1/8.
```

Set

```text
A=I-C^(-2) L L*,
K=-C^(-2) L* sum_(j=0)^(T-1) A^j f.                   (12)
```

This is a directly specified admissible parameter, using a polynomial
of fixed degree. Since `0<=A<=I` in the residual Hilbert space,

```text
f+LK=A^T f,
||f+LK||_2 <= e/4,
||K||_2 <= (T/C)e.                                    (13)
```

The second line follows by splitting the low spectral subspace in
(11) from its orthogonal complement. For operator norms, (10) gives
`||A||_(op->op)<=2`, and hence

```text
||K||_op <= ((2^T-1)/C) delta.                        (14)
```

No operator-norm bound for the spectral projection in (11) is used:
the actual correction is the polynomial (12).

Taylor's integral formula and (10) give

```text
||F(K)-f-LK||_2
 <= (C/2)||K||_op||K||_2
 <= T(2^T-1) delta e/(2C).                            (15)
```

Consequently, if

```text
delta <= C/(2T(2^T-1)),                               (16)
```

the exact vertex pair `Psi_q(K)` has residual at most `e/2`.
Its maximum normalized-HS generator displacement from `q` is at
most `(4T/C)e`. All constants are independent of matrix dimension.
This proves a concrete operator-small contracting step, with no
fourth- or sixth-moment flatness condition on the update.

## 4. What a flexible mixed construction would have to supply

Suppose a proposed preliminary operation, at every input of defect
`e`, produces an exact vertex pair `q` after padding `O(en)` and
generator-rank surgery `O(en)`, and has the following additional
properties with fixed constants:

* its HS residual is at most a fixed multiple of `e`;
* its operator residual satisfies (16);
* its residual component in the low singular subspace of `DF(0)`
  satisfies (11), with a fixed `sigma`.

Then Section 3 supplies an explicit contracting step. If the initial
multiple is larger than one, repeat the polynomial step enough times
to obtain contraction relative to the original defect, provided
(11) and (16) remain valid with the same constants at the intervening
outputs. The same closure condition is required on subsequent mixed
iterations. Alternatively, a preliminary residual bound `e(q)<=e`
already gives a one-step factor `1/2` under (11)--(16).

The surgery costs `O(sqrt(e))` in normalized HS norm, while the
polynomial correction costs `O(e)`. With uniform closure, geometric
defect decay makes the movements and relative padding summable. The
usual integer-dimension completion argument then gives an exact
finite-dimensional compatible endpoint. This is a sufficient scheme,
not a claim that the preliminary operation has been constructed.

Sections 1--2 solve two geometric issues with such an operation:
high/low splitting can remain within exact modular representations,
and a selected positive-central block can be made reducing at a
controlled rank cost. Neither result shows that the resulting residual
has small operator norm or satisfies (11). In particular, a uniform
nonzero singular-value gap at a compatible point does not imply
(11) at arbitrary inexact inputs: the residual may have a component
in a new small-singular subspace or outside the derivative's image.

Finally, a fixed operator threshold alone does not control a generic
square-root neutral correction. If `||K||_2=O(sqrt(e))`, the
second-order Taylor bound gives `O(theta sqrt(e))`, not `O(e)`.
Even a cubic remainder bound gives only
`O(theta^2 sqrt(e))`. Making that latter estimate `O(e)` requires
`theta=O(e^(1/4))`; the general spectral rank budget in (4) then
becomes `O(sqrt(e)n)`, rather than `O(en)`. A three-halves cubic
remainder would require `theta=O(sqrt(e))`, for which that rank
bound need not vanish relative to `n` at all. These upper-bound
calculations do not refute specially chosen directions, but they show
why deleting the sixth-flatness condition and inserting a fixed
operator cutoff is not a proof of the old neutral-quadratic step.

The constructive first-order polynomial update avoids this scaling
problem once the residual conditions (11) and (16) hold. Producing
those conditions with paid flexible surgery is the remaining task;
the lemmas do not infer it from low normalized-HS defect alone.
