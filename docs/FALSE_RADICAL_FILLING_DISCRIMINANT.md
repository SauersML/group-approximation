# Sofic-radical loops define canonical discriminant filling classes

Date: 2026-08-11

## 1. Purpose

`FALSE_DISCRIMINANT_PHASE_INSTABILITY.md` proves that a microscopic
discriminant subgroup with a nonzero radical-word character produces a
hyperlinear nonsofic image.  This note identifies that character directly
from the presentation complex.

The first point is group theoretic and standalone: a sofic-radical element
lies in the commutator subgroup of every finite-index subgroup.  Hence every
lift of its loop to every finite cover is an integral cellular boundary.
Orthogonally splitting any such integral filling produces a canonical class
in the cycle discriminant group.  That class is exactly the marked dual
class from Theorem 7 of the phase-instability note.

For regular finite covers, the classes over all vertices form a finite
deck-invariant **radical filling code**.  A microscopic covering radius and
one nonintegral entry of its discriminant Gram matrix are a complete FALSE
certificate.

## 2. Radical permanence under finite index

Write

`Rad_sof(H)=intersection_(phi:H->S, S sofic) ker(phi)`. `(RFD1)`

**Theorem 1 (finite-index radical permanence).**  If `K<=H` has finite
index, then

`Rad_sof(H)<=core_H(K)`                                `(RFD2)`

and

`Rad_sof(H)<=Rad_sof(K)`.                              `(RFD3)`

In particular,

`Rad_sof(H)<=intersection_([H:K]<infinity)[K,K]`.      `(RFD4)`

**Proof.**  The action of `H` on `H/K` has finite image.  Since finite
groups are sofic, every element of `Rad_sof(H)` lies in its kernel, which is
`core_H(K)`.  This proves `(RFD2)`.

Let `w in Rad_sof(H)` and let `phi:K->S` be a homomorphism to a sofic group.
Choose a transversal for `H/K`.  The usual induced cocycle gives a
homomorphism

`Ind(phi):H->S wr Sym(H/K)`.                           `(RFD5)`

The target is sofic: it is an extension of a finite direct power of `S` by
a finite group.  Therefore `Ind(phi)(w)=1`.  Since `w` belongs to the core
of `K`, the coordinate of `(RFD5)` at the trivial coset is `phi(w)`.
Consequently `phi(w)=1`.  This proves `(RFD3)`.

The abelianization of `K` is amenable and hence sofic.  Apply `(RFD3)` to
the quotient map `K->K_ab`; it kills `w`, so `w in [K,K]`.  This proves
`(RFD4)`.  End proof.

The use of an arbitrary sofic target in `(RFD5)` is stronger than needed
below.  For `(RFD4)` alone, one may induce a one-dimensional character of
`K`; its image is a finitely generated linear group and therefore
residually finite.

## 3. Integral fillings in finite presentation covers

Let

`H=<S|R>`                                               `(RFD6)`

be a finite presentation, let `Y` be its presentation `2`-complex, and let
`X=H/K` be a finite transitive `H`-set.  The associated Schreier complex
`Y_K` has cellular cochain map

`A_X=d_X^1:C^1(Y_K,R)->C^2(Y_K,R)`.                   `(RFD7)`

We use the cellular bases to identify chains and cochains by the Euclidean
inner product, so

`A_X^*=partial_(2,X)`.                                 `(RFD8)`

Fix `w in Rad_sof(H)`.  It fixes every vertex of `X`.  For `x in X`, let

`b_(w,x) in C_1(Y_K,Z)`                                `(RFD9)`

be the integral cellular cycle obtained by reading `w` from `x`.

**Theorem 2 (integral radical filling).**  For every `x in X`, there is

`z_(w,x) in C_2(Y_K,Z)`                                `(RFD10)`

such that

`A_X^* z_(w,x)=b_(w,x)`.                              `(RFD11)`

**Proof.**  The fundamental group of `Y_K` based at `x` is the stabilizer
`H_x`, a conjugate of `K`.  Theorem 1 gives

`w in Rad_sof(H_x)<= [H_x,H_x]`,                      `(RFD12)`

with the evident conjugation of the based word.  Thus the homology class of
the loop `(RFD9)` vanishes in

`H_1(Y_K,Z)=H_x^ab`.                                  `(RFD13)`

The cellular cycle `b_(w,x)` is therefore an integral cellular boundary,
which is exactly `(RFD10)--(RFD11)`.  End proof.

The theorem asserts existence, not a uniform filling norm.  Commutator
length in the finite-index subgroups may grow, and controlling the
orthogonal part of these fillings is one of the substantive metric gates
below.

## 4. The canonical filling class

Put

`W_X=ran_R(A_X)`,
`L_X=W_X intersect C^2(Y_K,Z)`,
`K_X=W_X^perp intersect C^2(Y_K,Z)`.                  `(RFD14)`

Let `p_W,p_K` be the orthogonal projections.  For a filling `(RFD10)`, set

`q_(w,x)=p_W z_(w,x)`, `u_(w,x)=p_K z_(w,x)`.         `(RFD15)`

**Theorem 3 (canonical marked filling class).**  The vector `q_(w,x)` and
the discriminant class

`c_(w,x)=u_(w,x)+K_X in K_X^#/K_X`                   `(RFD16)`

do not depend on the choice of the integral filling `z_(w,x)`.  Moreover,

`q_(w,x)=(A_X^dagger)^* b_(w,x) in L_X^#`,           `(RFD17)`

and under the canonical unimodular gluing

`gamma_X:K_X^#/K_X -> L_X^#/L_X`,                    `(RFD18)`

one has

`gamma_X(c_(w,x))=q_(w,x)+L_X`.                      `(RFD19)`

**Proof.**  If `z,z'` both fill `b_(w,x)`, then

`z-z' in ker(A_X^*)=W_X^perp`.                        `(RFD20)`

Because the difference is integral, it belongs to `K_X`.  Hence its
`W_X` projection is zero and its `K_X` projection changes `(RFD16)` by an
element of `K_X`.  This proves independence.

The restriction of `A_X^*` to `W_X` is injective.  Equations
`(RFD11)` and `(RFD15)` show that `q_(w,x)` is its unique solution of

`A_X^*q=b_(w,x)`,                                     `(RFD21)`

which is `(RFD17)`.  Finally, the integral vector

`z_(w,x)=q_(w,x)+u_(w,x)`                             `(RFD22)`

is precisely the orthogonal integral gluing construction.  It gives
`(RFD17)--(RFD19)`.  End proof.

Let `B_(w,X):C^1(Y_K,R)->R^X` be word evaluation: its `x`-th coordinate is

`(B_(w,X)y)_x=<b_(w,x),y>`.                           `(RFD23)`

Combining `(RFD17)` with adjointness gives, for
`a+L_X=gamma_X(c)`,

`(B_(w,X)A_X^dagger a)_x`
` =<q_(w,x),a> mod Z`.                                `(RFD24)`

Thus the `x`-th marked character from Theorem 7 of
`FALSE_DISCRIMINANT_PHASE_INSTABILITY.md` is represented by the canonical
class `q_(w,x)+L_X`, or equivalently by the paired filling class
`c_(w,x)`.

**Corollary 4.**  The `x`-th marked character on the full discriminant
group is nontrivial if and only if

`c_(w,x)!=0`,                                         `(RFD25)`

equivalently if and only if the canonical coexact filling `q_(w,x)` is not
integral.

## 5. The radical filling code

Now assume `K normal H`, so `X=H/K` is a regular finite cover.  Deck
transformations preserve the cellular bases, `A_X`, and the labelled
`w`-loops.  Define the deck-invariant finite subgroup

`C_(w,X)=<c_(w,x):x in X><=K_X^#/K_X`.               `(RFD26)`

Its discriminant Gram matrix is

`G_(w,X)(x,y)=<q_(w,x),q_(w,y)> mod Z`.               `(RFD27)`

**Theorem 5 (regular-cover FALSE certificate).**  Let `(X_n)` be regular
finite covers of the fixed presentation `(RFD6)`, with numbers of relator
cells `m_n`.  Suppose

`max_(c in C_(w,X_n)) rho_(K_Xn)(c)/sqrt(m_n)->0`,    `(RFD28)`

and for every sufficiently large `n` the matrix `(RFD27)` has a nonintegral
entry.  Then a hyperlinear nonsofic group exists.

**Proof.**  A nonintegral entry says that the coordinate character
represented by `q_(w,x)` is nontrivial on the generator `c_(w,y)` of the
filling code.  Deck transitivity makes all coordinate characters one orbit
and preserves `C_(w,X_n)`.  Hence Corollary 5 of
`FALSE_DISCRIMINANT_PHASE_INSTABILITY.md` supplies a class in the filling
code whose normalized word displacement is at least `sqrt(2)`.  Condition
`(RFD28)` makes its relator defect tend to zero.  The resulting tracial
matrix-ultraproduct image retains `w in Rad_sof(H)`, so it is hyperlinear
and nonsofic.  End proof.

The theorem is exact and finite at each stage.  The two quantities to
certify are:

1. the metric covering radius of the finite filling code in `(RFD28)`;
2. one nonzero entry of the rational matrix `(RFD27)` modulo `Z`.

No full discriminant enumeration is necessary for item 2.  The vectors in
`(RFD27)` are obtained by solving the real linear systems `(RFD21)`.

## 6. Concrete Kun--Thom target and limitations

The complete-radical calculation for the Kun--Thom symmetric double gives
a finitely generated group `D` with

`Rad_sof(D)=ker(D->G *_N G)`                           `(RFD29)`

and explicit nontrivial radical words

`x_h=i_2(h)i_1(h)^(-1)`.                              `(RFD30)`

After finite-presentation localization, fix a finite presentation `H` and
a word `w` mapping to one such surviving `x_h`.  Theorem 5 applies to every
regular finite quotient chart of this presentation.  It converts the
FALSE problem into the radical filling codes `(RFD26)`.

This is not yet the complete proof.  Theorem 2 supplies integral fillings
but no normalized bound `(RFD28)`.  Also, nontriviality of `w` does not by
itself force `(RFD27)` to be nonintegral: the canonical coexact fillings
could conceivably be integral in every finite cover.  These are now two
separate, checkable assertions rather than one unspecified projective-sector
problem.

The `p=53` projective `SL_3(Z)` harmonic quotient cannot be substituted
directly: `SL_3(Z)` is residually finite and has trivial sofic radical.
What can transfer is the method--a low-rank, microscopic filling code and a
nonzero discriminant Gram pairing--inside the finite covers of the radical
presentation `(RFD29)--(RFD30)`.
