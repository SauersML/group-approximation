# The Kazhdan decoder bounds the entire noninvariant orbit frame

Date: 2026-08-12

## 1. Outcome

The pointwise decoder in
`FALSE_NONAMENABLE_STABILIZER_FILLING_REDUCTION.md` is actually an
equivariant bounded operator on the whole deck orbit.  This closes the
remaining real-frame ambiguity in the constant-stabilizer tower.

Let

`K_n=pi^(-1)(L_n)`, `H_n=pi^(-1)(J L_n)`,
`A_n=H_n/K_n=J/(J intersect L_n)`, `m_n=|A_n|`,        `(KOF1)`

and let `b_(n,a)` be the `a`-translate of the marked loop in the `K_n`
cover.  Let `q_(n,a)` be its minimum real filling.  Define the filling
synthesis and marked analysis operators

`Q_n:ell^2(A_n)->C_2(Y_(K_n),C)`,
`Q_n delta_a=q_(n,a)`,                                `(KOF2)`

`T_n=Q_n^*`,
`(T_n y)(a)=<q_(n,a),y>`.                             `(KOF3)`

There is one constant `C_J`, independent of `n`, such that

`Fill_(R,2)(w;H_n)<=||T_n||_op`
` <=max{Fill_(R,2)(w;H_n),C_J}`.                     `(KOF4)`

The lower bound is the invariant orbit frame.  The upper bound is the new
operator statement: every nontrivial deck sector has a simultaneous
minimum filling operator of norm at most `C_J`.

Consequently:

1. if the intermediate real filling norms are unbounded, the marked ratio
   is unbounded and FALSE follows, as already proved by stabilizer-frame
   amplification;
2. if the intermediate real filling norms are bounded, the **entire real
   marked analysis operator is uniformly bounded**.

Thus low-capacity nonabelian Fourier concentration cannot occur in the
bounded-real branch of this explicit Kazhdan tower.  The nonabelian block
criterion in `FALSE_NONABELIAN_DECK_FRAME_BLOCKS.md` remains useful in
general, but here the Kazhdan right inverse forces all its block norms below
one fixed ceiling.

This does not bound the nonlinear marked discriminant ratio.  Indeed, the
tangent operator may stay bounded while integer/circle wells approach one
another at much smaller scales.  Combined with intermediate integral
filling escape, `(KOF4)` proves that the only surviving obstruction in the
bounded-real branch is the paired discriminant/carry geometry.  There is no
additional diffuse real-sector case to analyze.

## 2. The orbit synthesis maps

Fix a finite symmetric generating set `S` for the property-`(T)` stabilizer
`J`.  In the fixed presentation complex, choose finite two-chains `c_s`
satisfying

`partial_2 c_s=(s-1)b`, `s in S`.                    `(KOF5)`

These are fixed before passing to finite covers.  Write the same symbols
for their specializations.

On `ell^2(A_n)`, let

`D_n:directSum_(s in S)ell^2(A_n)->ell^2(A_n)`,
`D_n((xi_s))=sum_s xi_s(s-1)`.                       `(KOF6)`

Let `P_n` be averaging onto the constants.  Property `(T)` gives an
`A_n`-equivariant right inverse

`R_n:ell^2(A_n)->directSum_s ell^2(A_n)`             `(KOF7)`

such that

`D_nR_n=1-P_n`, `||R_n||<=C_0`                       `(KOF8)`

with `C_0` independent of `n`.  One canonical choice is the Moore--Penrose
right inverse

`R_n=D_n^*(D_nD_n^*)^(-1)(1-P_n)`.                  `(KOF9)`

The uniform spectral gap on `ell^2_0(A_n)` bounds `(KOF9)`, and because
`D_n` is right convolution, `R_n` commutes with left translation by `A_n`.

Define

`C_n:directSum_s ell^2(A_n)->C_2(Y_(K_n),C)`,
`C_n((xi_s))=sum_s xi_s c_s`.                        `(KOF10)`

Each `c_s` has fixed finite support.  The Schur/Young bound therefore gives

`||C_n||<=C_1`                                       `(KOF11)`

with `C_1` independent of `n`; `C_n` is also `A_n`-equivariant.

Finally define the word-orbit synthesis

`B_n:ell^2(A_n)->C_1(Y_(K_n),C)`,
`B_n delta_a=a b_n`.                                 `(KOF12)`

Equations `(KOF5)--(KOF6)` give the operator identity

`partial_2 C_n=B_nD_n`.                              `(KOF13)`

Hence

`U_n=C_nR_n`                                         `(KOF14)`

is an equivariant simultaneous decoder with

`partial_2U_n=B_n(1-P_n)`,
`||U_n||<=C_0C_1`.                                   `(KOF15)`

This is stronger than constructing one bounded chain for
`b_n-P_nb_n`: it fills every linear combination of the noninvariant orbit
with one uniform operator norm.

## 3. Orthogonal projection gives the minimum filling operator

Let

`E_n:C_2(Y_(K_n),C)->ker(partial_2)^perp`            `(KOF16)`

be orthogonal projection.  It commutes with the deck action and has norm
one.  The minimum filling synthesis in `(KOF2)` is

`Q_n=partial_2^dagger B_n`.                          `(KOF17)`

For every vector `f in (1-P_n)ell^2(A_n)`, equations `(KOF15)--(KOF17)`
show that `E_nU_nf` and `Q_nf` are both in
`ker(partial_2)^perp` and have the same boundary.  The boundary map is
injective on this subspace, so

`Q_n(1-P_n)=E_nU_n`.                                 `(KOF18)`

Consequently

`||Q_n(1-P_n)||<=C_0C_1`.                            `(KOF19)`

Put `C_J=C_0C_1`.

The invariant part is exact.  Let

`e_n=m_n^(-1/2) sum_(a in A_n)delta_a`               `(KOF20)`

be the unit constant vector.  Constant lift from the intermediate cover
shows that `Q_ne_n` is `m_n^(-1/2)` times the constant lift of the minimum
filling downstairs.  Therefore

`||Q_nP_n||_op=||Q_ne_n||`
` =Fill_(R,2)(w;H_n)`.                               `(KOF21)`

Both the domain decomposition

`ell^2(A_n)=P_n ell^2(A_n) directSum (1-P_n)ell^2(A_n)` `(KOF22)`

and the corresponding invariant/noninvariant decomposition of the range
are orthogonal.  Since `Q_n` is equivariant,

`||Q_n||_op`
` =max{||Q_nP_n||_op,||Q_n(1-P_n)||_op}`.            `(KOF23)`

Equations `(KOF19)--(KOF23)` prove the upper bound in `(KOF4)`.

For the lower bound, `(KOF21)` and `(KOF23)` give

`||Q_n||_op>=Fill_(R,2)(w;H_n)`.                    `(KOF24)`

Finally `T_n=Q_n^*`, so `||T_n||=||Q_n||`; this proves `(KOF4)`.

## 4. Fourier-block consequence

Decompose the complex two-chain representation of `A_n` as

`directSum_pi V_pi tensor M_pi`                      `(KOF25)`

and let `rho_(n,pi)` be the reduced densities of `q_(n,1)` from
`FALSE_NONABELIAN_DECK_FRAME_BLOCKS.md`.  Its exact formula and `(KOF4)`
give, for every nontrivial `pi`,

`(m_n/d_pi)||rho_(n,pi)||_op<=C_J^2`.                `(KOF26)`

Thus

`||rho_(n,pi)||_op<=C_J^2 d_pi/m_n`.                 `(KOF27)`

This is precisely the Plancherel-flat block estimate that the general
nonabelian theorem had isolated as the only escape from real-frame
amplification.  In this tower it is forced automatically by the Kazhdan
decoder.

The invariant block instead has eigenvalue

`Fill_(R,2)(w;H_n)^2`.                               `(KOF28)`

Therefore all possible unbounded real frame growth is exactly the one
intermediate transfer mode already measured downstairs.  Once that mode is
bounded, no other real Fourier sector can revive the FALSE proof.

## 5. Exact remaining gate

Along the relatively separating tower, the word has infinite order in the
limiting intermediate homology, so

`Fill_(Z,2)(w;H_n)->infinity`.                        `(KOF29)`

If the real fills in `(KOF21)` remain bounded, the discriminant Pythagoras
identity forces

`rho_(H_n)(c_(H_n))->infinity`.                       `(KOF30)`

The operator theorem proves that `(KOF30)` cannot be accompanied by a
hidden real-frame concentration.  The sole remaining question is now:

> Do the canonical low-carry discriminant classes have unbounded marked
> Gram/incidence ratio, or does total isotropy imply a uniformly bounded
> integral filling?

The first alternative proves FALSE by the marked discriminant divergence
criterion.  The second would be a genuine integral decoder theorem.  No
additional real harmonic or nonabelian deck-spectrum case remains between
them.

