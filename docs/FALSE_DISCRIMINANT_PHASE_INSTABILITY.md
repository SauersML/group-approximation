# Macroscopic discriminant classes produce nonliftable phase microstates

Date: 2026-08-11

## 1. Purpose

`INTEGRAL_CARRY_DISCRIMINANT_DUALITY.md` identifies the exact circle-repair
constant of an integral linear map with paired shortest-vector radii in two
discriminant lattices.  This note extracts the converse, FALSE-side content
of that formula.

The important regime is not merely a divergent ratio.  It is a class whose
cycle-side representative is microscopic in normalized dimension while its
glued range-side representative is macroscopic.  Such a class gives phase
tables with vanishing normalized relator defect which nevertheless remain a
fixed normalized distance from every exact phase table.

This is a genuine flexible-stability obstruction.  It does not by itself
produce a hyperlinear nonsofic group: the remaining marked-word condition is
stated explicitly in Section 4.

## 2. Normalized integral setup

For each `n`, let

`A_n:R^(e_n) -> R^(m_n)`                                 `(DPI1)`

be an integral matrix.  Equip its domain and range with normalized Euclidean
norms

`||x||_(E,n)=||x||_2/sqrt(e_n)`,
`||y||_(F,n)=||y||_2/sqrt(m_n)`.                         `(DPI2)`

Put

`W_n=ran_R(A_n)`, `L_n=W_n intersect Z^(m_n)`,
`K_n=W_n^perp intersect Z^(m_n)`.                        `(DPI3)`

Let `D_(K,n)=K_n^#/K_n` and let

`gamma_n:D_(K,n) -> L_n^#/L_n`                          `(DPI4)`

be the unimodular gluing isomorphism of Proposition 1 in the discriminant
note.  Write `rho_K(c)` and `rho_L(gamma_n(c))` for the corresponding
shortest-coset radii.

Let `A_n^dagger:W_n->ker(A_n)^perp` be the Moore--Penrose inverse and define
the paired ellipsoidal radius

`rho_(A,L)(d)=min{||A_n^dagger a||_2:
                  a in L_n^#, a+L_n=d}`.              `(DPI4a)`

Unlike the Euclidean radius `rho_L`, this is the exact metric seen by phase
repair in the domain.

The additive phase defect and repair distance are

`def_n(x)=dist_(F,n)(A_n x,Z^(m_n))`,                   `(DPI5)`

`rep_n(x)=dist_(E,n)(x,A_n^(-1)(Z^(m_n)))`.            `(DPI6)`

Assume throughout that

`||A_n||_(E,n -> F,n)<=C`                               `(DPI7)`

for one constant `C`.  For relator matrices of a fixed finite presentation,
`(DPI7)` follows from the fixed row and column incidence bounds.

## 3. The macroscopic discriminant theorem

**Theorem 1 (paired-radius instability).**  For every nonzero
`c in D_(K,n)`, there is `x_c in R^(e_n)` such that

`def_n(x_c)<=rho_K(c)/sqrt(m_n)`,                       `(DPI8)`

`rep_n(x_c)=rho_(A,L)(gamma_n(c))/sqrt(e_n)`
`          >=rho_L(gamma_n(c))/(C sqrt(m_n))`.          `(DPI9)`

Consequently, if classes `0!=c_n in D_(K,n)` satisfy

`rho_K(c_n)/sqrt(m_n)->0`,                              `(DPI10)`

`liminf_n rho_(A,L)(gamma_n(c_n))/sqrt(e_n)>0`,         `(DPI11)`

then the induced torus maps have approximate zeros with vanishing normalized
defect which remain a fixed normalized distance from every exact zero.

**Proof.**  Choose a shortest representative

`u in K_n^#`, `u+K_n=c`, `||u||_2=rho_K(c)`.           `(DPI12)`

Unimodular gluing supplies `z in Z^(m_n)` with

`p_(K_n)z=u`, `p_(W_n)z=a`,                            `(DPI13)`

where the class of `a` modulo `L_n` is `gamma_n(c)`.  Thus

`dist_2(a,L_n)=rho_L(gamma_n(c))`.                      `(DPI14)`

Choose `x_c` perpendicular to `ker(A_n)` with

`A_n x_c=a=z-u`.                                       `(DPI15)`

We may change `a` by any element of `L_n` and change `x_c` by its canonical
`A_n^dagger` lift without changing `(DPI13)` or the class.  Choose this
translate to minimize the ellipsoidal norm.  The exact quotient-norm formula
for circle repair then gives

`rep_n(x_c)=rho_(A,L)(gamma_n(c))/sqrt(e_n)`.           `(DPI15a)`

The integer vector `z` is an admissible competitor in `(DPI5)`, so

`def_n(x_c)<=||u||_2/sqrt(m_n)`,                        `(DPI16)`

which is `(DPI8)`.

If `y` is any exact phase table, then `A_n y` belongs to

`W_n intersect Z^(m_n)=L_n`.                            `(DPI17)`

Equations `(DPI14)--(DPI15)` also give

`||A_n(x_c-y)||_2>=rho_L(gamma_n(c))`.                  `(DPI18)`

After normalizing and applying `(DPI7)`,

`C||x_c-y||_(E,n)>=rho_L(gamma_n(c))/sqrt(m_n)`.       `(DPI19)`

Taking the infimum over exact `y` proves `(DPI9)`.  The final assertion is
immediate.  End proof.

The defect side is exact as well if one retains the lower envelope rather
than only its easiest upper bound.  Among the finitely many ellipsoidal
shortest representatives used in `(DPI15a)`, choose `a_c` with least
distance to `Z^(m_n)` and put

`delta_A(c)=dist_2(a_c,Z^(m_n))`.                       `(DPI19a)`

If `d_(gamma d)(a_c)` denotes Euclidean distance from `a_c` to the coset
`gamma(d) subset L_n^#`, the nonlinear discriminant formula gives

`delta_A(c)^2=min_(d in D_(K,n))`
`  (d_(gamma d)(a_c)^2+rho_K(d)^2)`.                  `(DPI19b)`

For `d=c` the first summand is zero, so

`delta_A(c)<=rho_K(c)`.                                `(DPI19c)`

Thus the canonical phase table has the exact paired geometry

`def_n(x_c)=delta_A(c)/sqrt(m_n)`,
`rep_n(x_c)=rho_(A,L)(gamma_n(c))/sqrt(e_n)`.          `(DPI19d)`

The conclusion is unchanged after passing from additive geodesic distance
on `R/Z` to chordal distance on `T`, up to universal constants.  Integer
translations of `x_c-y` do not weaken `(DPI9)`: applying `A_n` merely changes
the competitor in `L_n` by an element of `A_n(Z^(e_n)) subset L_n`.

**Corollary 2 (exact paired criterion).**  The canonical paired microstates
have vanishing defect and macroscopic repair distance exactly when

`delta_A(c_n)=o(sqrt(m_n))`

and

`rho_(A,L)(gamma_n(c_n))=Omega(sqrt(e_n))`.             `(DPI20)`

The easier-to-check sufficient condition for the first line is

`rho_K(c_n)=o(sqrt(m_n))`

by `(DPI19c)`.

Under `(DPI7)`, the simpler Euclidean condition

`rho_L(gamma_n(c_n))=Omega(sqrt(m_n))`                 `(DPI20a)`

is sufficient for the second half of `(DPI20)`.

In particular, divergence of

`Theta(A_n)^2=1+rho_L(gamma_n(c_n))^2/rho_K(c_n)^2`    `(DPI21)`

is not enough: both numerator and denominator could be submacroscopic.
The two-scale condition `(DPI20)` is the correct normalized-Hilbert--Schmidt
target.

## 4. From instability to a hyperlinear nonsofic image

Suppose now that `A_n` are the phase-relator matrices obtained from exact
finite permutation charts of a fixed finite presentation

`H=<S|R>`.                                               `(DPI22)`

Exponentiating `x_c` coordinatewise and multiplying by the exact permutation
matrices gives monomial maps

`Phi_n:S->U(N_n)`.                                      `(DPI23)`

For each fixed relator, its normalized Hilbert--Schmidt defect is bounded by
a presentation-dependent constant times `(DPI8)`.  Hence `(DPI10)` makes
`(Phi_n)` an asymptotic unitary representation.

The repair obstruction `(DPI11)` says that these maps cannot be changed to
exact phase cocycles over the same permutation charts by an `o(1)` normalized
Hilbert--Schmidt perturbation.  It does not identify which group element is
retained.  The following marked condition is the exact additional datum.

There is a completely finite-dimensional way to compute that datum.  Fix
`w in Rad_sof(H)`.  Every exact finite permutation action of `H` kills `w`:
its image is finite, hence sofic, and the definition of the sofic radical
applies.  Therefore the permutation part of the monomial matrix `Phi_x(w)`
is the identity.  Collecting the phases encountered along the word gives an
integral word-evaluation matrix

`B_(w,n):R^(e_n)->R^(N_n)`                             `(DPI24a)`

such that

`Phi_x(w)=diag(exp(2 pi i (B_(w,n)x)_j))_(j=1)^(N_n)`. `(DPI24b)`

Define its normalized marked chordal value by

`mu_(w,n)(x)^2=(1/N_n) sum_j |exp(2 pi i
(B_(w,n)x)_j)-1|^2`.                                  `(DPI24c)`

For a discriminant representative `(DPI13)`, take the canonical lift

`x_c=A_n^dagger p_(W_n)z`,                             `(DPI24d)`

where `A_n^dagger` is the Moore--Penrose inverse.  This is exactly the
choice perpendicular to `ker(A_n)` made in `(DPI15)`.  Thus all three tests
below are finite lattice/linear-algebra computations: `rho_K(c)`, the exact
ellipsoidal radius `rho_(A,L)(gamma_n(c))`, and `mu_(w,n)(x_c)`.  The
Euclidean `rho_L` gives the cheaper sufficient test `(DPI20a)`.

**Theorem 3 (marked discriminant criterion).**  In the situation above,
let

`1!=w in Rad_sof(H)`.                                    `(DPI24)`

If the classes `c_n` satisfy `(DPI10)` and can be chosen so that

`liminf_n ||Phi_n(w)-1||_(2,N_n)>0`,                    `(DPI25)`

then a hyperlinear nonsofic group exists.  If `(DPI11)` also holds, the same
models are moreover a macroscopic flexible-stability obstruction.

**Proof.**  The maps `(DPI23)` define a homomorphism from `H` into a tracial
matrix ultraproduct.  Equation `(DPI25)` says that its image retains `w`, so
the image is nontrivial and hyperlinear.  If the image were sofic, the
quotient homomorphism from `H` to it would kill every element of
`Rad_sof(H)`, contradicting `(DPI24)--(DPI25)`.  End proof.

By `(DPI24b)--(DPI24c)`, condition `(DPI25)` is precisely

`liminf_n mu_(w,n)(A_n^dagger p_(W_n)z_n)>0`.          `(DPI26)`

This removes the last qualitative phrase from the certificate.  A sequence
of exact integer data

`(A_n,B_(w,n),z_n)`                                    `(DPI27)`

proves the desired FALSE result once its cycle-side projection satisfies
`(DPI10)` and the explicit chordal test `(DPI26)`.  Adding the paired
range-side condition `(DPI11)` independently certifies that the microstates
are not merely exact cocycles in disguise; it is also the natural geometric
search criterion supplied by discriminant duality.

Thus the discriminant program has a sharp FALSE-side certificate:

1. a microscopic cycle-side radius `(DPI10)`;
2. a macroscopic glued ellipsoidal range-side radius `(DPI11)`;
3. a fixed-word evaluation `(DPI25)` on a known sofic-radical word.

Items 1 and 2 prove nonliftable phase microstates.  Items 1 and 3 prove the
desired group counterexample.  All three together produce a hyperlinear
nonsofic image witnessed by a macroscopic integral repair obstruction.

## 5. Calibration and computation target

For the oriented incidence matrix of a connected `d`-regular graph on `n`
vertices, the class computed in the discriminant note has

`rho_K=1/sqrt(n)`, `rho_L=sqrt(1-1/n)`.                 `(DPI28)`

Here `m_n=n`, so both normalized radii tend to zero.  The repair constant is
of order `sqrt(n)`, but the instability is not macroscopic in normalized
dimension.  This example proves why the ratio alone cannot drive the FALSE
construction.

For the projective `SL_3(Z)` charts, the useful exact computation is
therefore not only the shortest dual vector or the regulator.  One must also
compute its glued `L_n^#/L_n` representative and test whether its norm is of
order `sqrt(m_n)`.  The strong candidate is a harmonic dual vector with
sub-square-root norm paired, under unimodular gluing, to a delocalized
range-lattice class of square-root norm.  Finally its phase evaluation must
be paired with one fixed radical word as in `(DPI25)`.
