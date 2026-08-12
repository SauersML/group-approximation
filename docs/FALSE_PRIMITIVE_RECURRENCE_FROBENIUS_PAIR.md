# Primitive recurrences give equal-order Frobenius sectors with an inverse fold

Date: 2026-08-12

## 1. Outcome

The monodromy obstruction in
`FALSE_LONG_CHAIN_BUNDLE_MONODROMY_NO_GO.md` is specific to putting one
coefficient shear into a cyclic chain.  There is a different finite
Frobenius construction in which the two compressors have the **same exact
order**, agree for an arbitrarily long positive polynomial window, and still
have a macroscopic inverse fold.

Fix a finite field `k=F_l` and an integer `n>=3`.  There are two finite field
models

`B_i=k[x]/(f_i(x)) ~= F_(l^n)`, `i=0,1`,              `(PRF1)`

where `f_0,f_1` are distinct primitive polynomials of degree `n`.  After
identifying both fields with the common coefficient space

`W_n=k e_0 directSum ... directSum k e_(n-1)`,         `(PRF2)`

multiplication by `x` gives two operators `T_0,T_1` such that

`T_0^j e_0=T_1^j e_0=e_j`, `0<=j<n`,                 `(PRF3)`

but

`T_0^(-1)e_0 != T_1^(-1)e_0`.                        `(PRF4)`

Both `T_i` have exact order `l^n-1`.  On `ell^2(W_n)`, finite Fourier
duality turns them into permutation compressor unitaries `U_i` and turns
the vectors in `(PRF2)` into character multipliers `Z(v)`.  Then

`Ad(U_0^j)(Z(e_0))=Ad(U_1^j)(Z(e_0))`
`                         =Z(e_j)`, `0<=j<n`,          `(PRF5)`

while

`||Ad(U_0^(-1))(Z(e_0))`
`  -Ad(U_1^(-1))(Z(e_0))||_2^2=2`.                   `(PRF6)`

Thus the common positive arc has length `n`, the inverse fold has constant
energy, and there is no analogue of the compulsory extra factor
`p^(n-1)` in the compressor order `(LCM18)`.

There is also a ring-window statement.  For every fixed positive polynomial
window of degree at most `D`, choosing `n>2D` makes the two quotient algebras
literally identical on all additions and multiplications occurring in that
window.  The difference is first visible through the inverse recurrence.

This closes a local finite-Frobenius problem which the long cyclic chain did
not close.  It does **not** yet give representations of the Kun--Thom vertex
groups.  The two recurrence fields must still be transported coherently
under the other external substitutions.  Moreover, exact Kazhdan-covariant
completion would kill the fold by
`FALSE_KAZHDAN_CYCLIC_SEED_TRACIAL_EXTENSION.md`.  The remaining
globalization must therefore retain genuinely nonliftable approximate
tangent covariance.

## 2. Two distinct primitive recurrences always exist

Choose a primitive element `alpha in F_(l^n)` and let `f_0` be its minimal
polynomial over `k`.  The inverse `alpha^(-1)` is also primitive; let `f_1`
be its minimal polynomial.

For `n>=3`, these polynomials are distinct.  Otherwise `alpha^(-1)` would be
a Frobenius conjugate of `alpha`, so

`alpha^(-1)=alpha^(l^j)`                              `(PRF7)`

for some `0<=j<n`.  Since `alpha` has order `l^n-1`, this would imply

`l^j=-1 mod (l^n-1)`.                                `(PRF8)`

But

`0<l^j+1<=l^(n-1)+1<l^n-1`                          `(PRF9)`

for `n>=3`, except that the last strict inequality only needs separate
inspection at `(l,n)=(2,2)`, which is outside the stated range.  Thus
`(PRF8)` is impossible.

Write

`f_i(X)=X^n+a_(i,n-1)X^(n-1)+...+a_(i,1)X+a_(i,0)`, `(PRF10)`

where `a_(i,0)!=0`.  Use the coefficient-basis identification

`1 |->e_0`, `x|->e_1`, ..., `x^(n-1)|->e_(n-1)`      `(PRF11)`

for both quotients.  Multiplication by `x` is an invertible `k`-linear map
`T_i`.  Equation `(PRF3)` is immediate from `(PRF11)`.  Since the class of
`x` is primitive in `B_i^x`, both maps have exact order `l^n-1`.

Dividing `(PRF10)` by `x` in `B_i` gives the exact inverse formula

`T_i^(-1)e_0`
` =-a_(i,0)^(-1)(e_(n-1)+a_(i,n-1)e_(n-2)`
`                      +...+a_(i,2)e_1+a_(i,1)e_0).` `(PRF12)`

The vector in `(PRF12)` determines every coefficient of the monic
polynomial `(PRF10)`: its `e_(n-1)` coordinate determines `a_(i,0)`, and
the remaining coordinates then determine `a_(i,1),...,a_(i,n-1)`.
Therefore equality of the two inverse vectors would imply `f_0=f_1`,
contrary to the preceding paragraph.  This proves `(PRF4)`.

## 3. Exact Fourier realization

Fix a nontrivial additive character

`psi:k->T`                                           `(PRF13)`

and use the standard dot product on `W_n`.  For `v in W_n`, define the
character multiplier

`Z(v) delta_y=psi(y dot v) delta_y`, `y in W_n`.      `(PRF14)`

Then

`Z(v+v')=Z(v)Z(v')`.                                 `(PRF15)`

For `i=0,1`, let `U_i` be the permutation unitary induced by the
contragredient map:

`U_i delta_y=delta_((T_i^(-1))^T y).`                `(PRF16)`

Direct substitution in `(PRF14)` gives

`U_i Z(v)U_i^(-1)=Z(T_i v).`                         `(PRF17)`

The order of `U_i` equals the order of `T_i`, namely `l^n-1`.  Combining
`(PRF3)` and `(PRF17)` proves `(PRF5)`.

Put

`d=T_1^(-1)e_0-T_0^(-1)e_0 !=0`.                    `(PRF18)`

The quotient of the two inverse character multipliers is `Z(d)`.  A
nontrivial character has zero average on the finite additive group, so

`tr_(ell^2(W_n))(Z(d))=0`.                            `(PRF19)`

For unitaries `A,B`,

`||A-B||_2^2=2-2 Re tr(A^*B)`.                       `(PRF20)`

Equations `(PRF17)--(PRF20)` prove `(PRF6)`.

The whole construction is regular and exact: no approximate matrix
relation, spectral matching, or boundary deletion occurs.

## 4. The bounded positive ring window is identical

Let `P_D` be the `k`-space of polynomials of degree at most `D`.  If
`n>D`, both quotient maps

`P_D -> B_i`                                         `(PRF21)`

are injective, and under `(PRF11)` they are the same linear map into
`W_n`.  If `n>2D`, then for `a,b in P_D` their ordinary product has degree
less than `n`.  Consequently

`j_0(a+b)=j_1(a+b)`,
`j_0(ab)=j_1(ab)`                                    `(PRF22)`

under the common coefficient identification, with no reduction by either
`f_i`.

More generally, take any fixed finite list of positive polynomial
expressions.  Let `D` bound the degrees of all intermediate additions and
multiplications appearing in that list.  Every identity in the list has
the same coefficient table in `B_0` and `B_1` once `n>D`.  Meanwhile
`(PRF12)` shows that the inverse label remains different.

Because finite fields are Frobenius algebras, the trace pairing

`(u,v)_i=Tr_(B_i/k)(uv)`                              `(PRF23)`

is perfect.  Hence each sector can be fed into the paired regular/Fourier
module functor of `FALSE_PAIRED_FOURIER_FINITE_MODULE_FUNCTOR.md`.  For
square-zero tangent layers one may also tensor `(PRF23)` with the matrix
trace pairing and the coefficient-module pairing exactly as in
`FALSE_LONG_FROBENIUS_ELEMENTARY_COMPRESSOR.md`.

## 5. What this changes in the FALSE route

The old long-chain cell used one cyclic polarization orbit and inserted a
coefficient shear at its wrap.  Its second compressor necessarily had order
larger by the full shear order, and exact principal-bundle coinduction then
spread the mismatch over density `1-o(1)`; see `(LCM16)--(LCM23)`.

The primitive-recurrence pair changes the architecture:

1. the two sectors use different recurrence fields rather than one field
   with a sheared wrap;
2. their compressor orders are exactly equal;
3. every bounded positive coefficient computation occurs before either
   recurrence is visible; and
4. the inverse coefficient detects the difference with energy exactly two.

Therefore the **order-inflation** and **orbitwise monodromy-density**
arguments from the long-chain no-go do not apply to this pair.

Two serious gates remain.

First, the external group `SL_d(Z)` mixes Laurent monomials in several
directions.  One must transport the two recurrence ideals over a finite
external base so that all fixed substitution and Steinberg windows have
vanishing normalized HS defect.  A constant fiber is impossible by
`FALSE_PRINCIPAL_BUNDLE_CONSTANT_COEFFICIENT_NO_GO.md`; the recurrence field
must vary with the base point or be coupled by higher incidence.

Second, if the resulting base and tangent covariance were simultaneously
correctable to exact representations on a fixed Kazhdan window, then the
cyclic-seed propagation theorem would bound the inverse fold by the same
vanishing defect.  Thus the desired external transport must be a genuine
normalized-Hilbert--Schmidt instability sequence, not merely an awkward
presentation of exact finite quotients.

The next finite target is consequently precise: place the two recurrence
fields over one external Schreier model, measure only the fixed
substitution/Steinberg window, and test whether their coefficient charts can
be matched off an `o(1)` fraction while the inverse vectors `(PRF12)` retain
positive Fourier mass.  Dense-unitary optimization is unnecessary; all
local matrices are companion, permutation, and finite Fourier matrices.
