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

The construction actually gives a growing family, not only two sectors.
Let `calP_n` be the set of monic primitive polynomials of degree `n` over
`F_l`.  Primitive elements of `F_(l^n)` occur in Frobenius orbits of size
exactly `n`, and every such orbit has one minimal polynomial.  Therefore

`|calP_n|=phi(l^n-1)/n`.                              `(PRF12a)`

This quantity tends to infinity with `n`.  For every `f in calP_n`, let
`T_f` be multiplication by `x` in the coefficient basis `(PRF11)`.  All
these maps have order `l^n-1` and satisfy

`T_f^j e_0=e_j`, `0<=j<n`.                           `(PRF12b)`

The injectivity argument following `(PRF12)` shows that the inverse vectors

`v_f=T_f^(-1)e_0`                                    `(PRF12c)`

are pairwise distinct.  Thus one obtains
`phi(l^n-1)/n` equal-order sectors with one literally common positive arc
and pairwise distinct inverse labels.  Section 3 shows that their inverse
Fourier operators are pairwise separated by squared normalized HS distance
two.  This is a growing higher-incidence alphabet, not a balanced
one-dimensional wall system.

There is a stronger coding form.  Give `W_n=k^n` coordinate Hamming metric.

**Proposition 1 (primitive inverse code).**  For every fixed finite field
`F_l`, there are constants `delta_l,c_l>0` and, for all sufficiently large
`n`, subfamilies

`C_n subset calP_n`, `|C_n|>=l^(c_l n)`,              `(PRF12d)`

such that

`d_H(v_f,v_g)>=delta_l n`                            `(PRF12e)`

for all distinct `f,g in C_n`.

**Proof.**  There are `phi(l^n-1)/n=l^(n-o(n))` primitive polynomials.
Their nonzero constant terms take only `l-1` values, so one constant-term
fiber still has cardinality `l^(n-o(n))`.  On that fiber, formula `(PRF12)`
identifies the remaining polynomial coefficient vector with `v_f` by one
fixed coordinate reversal and multiplication by a nonzero scalar.  It
therefore preserves Hamming distance.

Choose `delta_l>0` so small that the `l`-ary entropy satisfies
`H_l(delta_l)<1`.  A Hamming ball of radius `delta_l n` in `k^n` has size at
most `l^((H_l(delta_l)+o(1))n)`.  Greedily select a vector and delete its
ball.  Since the starting constant-term fiber has exponent `1-o(1)`, the
remaining code has positive exponential rate for all large `n`.  Pulling it
back through `(PRF12)` proves `(PRF12d)--(PRF12e)`.  End proof.

Thus the common positive arc supports not only many distinguishable inverse
sectors, but an honest positive-rate code of inverse sectors.  This is the
finite combinatorial resource required by a higher-incidence carry scheme:
local transport would have to change few inverse coordinates per tested
relation while a marked path crosses a linear code distance.

The Hamming statement already has a compressed Fourier consequence.  Fix a
nontrivial additive character `psi:k->T`.  On
`ell^2({0,...,n-1} times k)`, put

`Z_coord(v)delta_(j,y)=psi(y v_j)delta_(j,y)`.        `(PRF12f)`

If `v_j!=w_j`, the average over `y in k` of
`psi(y(w_j-v_j))` is zero.  Hence

`||Z_coord(v)-Z_coord(w)||_2^2=2 d_H(v,w)/n`.         `(PRF12g)`

In particular, `(PRF12e)` gives

`||Z_coord(v_f)-Z_coord(v_g)||_2^2>=2 delta_l`.       `(PRF12h)`

Thus linear inverse-code distance already yields macroscopic normalized HS
separation in dimension `n`, rather than only in the full regular dimension
`l^n`.  The missing operation on this compressed model is a low-defect
unitary transport implementing the companion recurrences: the coordinate
character set is not invariant under a dense feedback row.  Equation
`(PRF12h)` isolates exactly what such a sparse transport must preserve.

There is a sharp warning: an honest Kazhdan action cannot transport this
code with vanishing local Hamming cost and macroscopic endpoint cost.

**Proposition 2 (Kazhdan sector-code inequality).**  Let a group `Gamma`
with finite symmetric Kazhdan set `S` and Kazhdan constant `kappa` act on a
finite set `X`.  For every map

`c:X->k^n`                                            `(PRF12i)`

and every `g in Gamma`,

`E_x d_H(c(gx),c(x))/n`
` <=(4/kappa^2) max_(s in S) E_x d_H(c(sx),c(x))/n`. `(PRF12j)`

**Proof.**  Embed `k^n` into the unit sphere of
`H_0=directSum_(j=1)^n ell^2(k)` by

`Phi(a_1,...,a_n)=n^(-1/2) directSum_j delta_(a_j).` `(PRF12k)`

Then

`||Phi(a)-Phi(b)||^2=2d_H(a,b)/n`.                   `(PRF12l)`

Regard `F(x)=Phi(c(x))` as a vector in `ell^2(X;H_0)` with normalized
counting measure, and let `P` be projection onto the invariant vectors for
the permutation action of `Gamma` on the `X` coordinate.  The Kazhdan
inequality gives

`||F-PF|| <=kappa^(-1) max_(s in S)||sF-F||`.         `(PRF12m)`

Since `PF` is invariant,

`||gF-F||<=2||F-PF||`.                               `(PRF12n)`

Square `(PRF12m)--(PRF12n)` and use `(PRF12l)`.  This is
`(PRF12j)`.  End proof.

Therefore a path through the inverse code cannot by itself beat property
`(T)`: if a fixed marked group element crosses linear relative code
distance, some fixed Kazhdan generator also crosses linear relative code
distance.  The only surviving use is the intended one--put the code into a
sequence of approximate base/tangent actions which stays uniformly far
from every exact action.  Proposition 2 is the coordinate-code version of
the tracial cyclic-seed obstruction, and prevents mistaking the local code
for a completed FALSE proof.

In fact the most direct compressed transport is already impossible before
property `(T)` enters.  Retain `(PRF12f)` and, for

`f(X)=X^n+a_(n-1)X^(n-1)+...+a_1X+a_0`,              `(PRF12o)`

put

`w(f)=|{r in {1,...,n-1}:a_r!=0}|`.                  `(PRF12p)`

Let `pi_coord(v)=Z_coord(v)`.  Define the optimal full-additive covariance
cost

`epsilon(f)^2=inf_(U in U(n|k|)) E_(v in k^n)`
` ||U pi_coord(v)U^*-pi_coord(T_fv)||_2^2`.           `(PRF12q)`

**Proposition 3 (feedback-support identity and compressed no-go).**

`epsilon(f)^2=2(l-1)w(f)/(ln)`.                      `(PRF12r)`

If `f,g` have the same constant term, then

`||Z_coord(v_f)-Z_coord(v_g)||_2^2`
` <=(l/(l-1))(epsilon(f)^2+epsilon(g)^2).`            `(PRF12s)`

Consequently no pair of compressed coordinate models can have both
covariance costs tending to zero and inverse-fold energy bounded below.

**Proof.**  The character multiset of `pi_coord` consists of the zero
character with multiplicity `n`, and every nonzero character on each of the
`n` coordinate lines with multiplicity one.  The transformed multiset uses
the lines spanned by `T_f^T e_r`.  In the companion basis,

`T_f^T e_0=-a_0e_(n-1)`,
`T_f^T e_r=e_(r-1)-a_re_(n-1)`, `1<=r<n`.            `(PRF12t)`

The first is a coordinate line.  For `r>=1`, the second is a coordinate
line exactly when `a_r=0`; when `a_r!=0` it is an oblique line, and the
different pivot coordinates make all such lines distinct.  The two
character multisets therefore have exactly `w(f)(l-1)` unmatched nonzero
characters out of total dimension `nl`.

Match every common character space and pair the remaining one-dimensional
spaces arbitrarily.  Distinct finite characters have average squared
chordal distance two.  Conversely character orthogonality shows that no
unitary can match more than the common multiplicities.  Hence the optimal
average is exactly twice the unmatched fraction, proving `(PRF12r)`.

On a fixed constant-term fiber, `(PRF12)` says that the inverse-vector
Hamming distance is the Hamming distance between the coefficient rows
`(a_1,...,a_(n-1))`.  It is at most `w(f)+w(g)`.  Equation `(PRF12g)` gives

`||Z_coord(v_f)-Z_coord(v_g)||_2^2`
` <=2(w(f)+w(g))/n`.                                  `(PRF12u)`

Substitute `(PRF12r)` for `f` and `g` to obtain `(PRF12s)`.  End proof.

Proposition 3 closes the tempting plan “pack the primitive inverse code and
transport only its coordinate characters.”  Linear code distance requires
linear feedback support, and the exact character mismatch sees that support
with constant normalized cost.  A live higher-incidence construction must
couple different feedback rows so their local unmatched character mass
cancels or is shared; independent coordinate blocks cannot work.

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

The same calculation applies to every pair `f!=g` in `calP_n`: by
`(PRF12c)`, `v_f-v_g!=0`, so

`||Z(v_f)-Z(v_g)||_2^2=2`.                            `(PRF20a)`

Consequently all `|calP_n|` inverse sectors are mutually equidistant in
normalized Hilbert--Schmidt metric while their first `n` forward sectors
coincide.

The whole construction is regular and exact: no approximate matrix
relation, spectral matching, or boundary deletion occurs.

### Smallest example

Over `F_2`, take

`f_0(X)=X^3+X+1`, `f_1(X)=X^3+X^2+1`.               `(PRF20b)`

These are the two primitive cubics.  Both compressor maps have order seven
and agree on `1,x,x^2`.  Formula `(PRF12)` gives

`T_0^(-1)e_0=e_2+e_0`,
`T_1^(-1)e_0=e_2+e_1`.                               `(PRF20c)`

Their difference is `e_0+e_1!=0`.  Thus even the seven-point Singer cycle
already exhibits the equal-order inverse-fold phenomenon; increasing `n`
only lengthens the common positive window and increases the number of
available primitive sectors.

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

Moreover `(PRF12a)--(PRF20a)` provide a growing number of such sectors.
This is the first explicit local Frobenius cell in this route with both
unbounded incidence and no compressor-order inflation.

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
