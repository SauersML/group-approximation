# A fixed-prime tower with constant Kazhdan transfer degree

Date: 2026-08-11

## 1. Outcome

For the stable Laurent double, fix one prime `p`.  There is an explicit
nested sequence of normal finite-index subgroups

`L_1>=L_2>=... normal F=G *_E G`                         `(FPC1)`

such that

`intersection_n L_n=E(p)`,
`intersection_n J L_n=J E(p)`,                           `(FPC2)`

where

`E(p)=ker(E->EL_r(F_p[x_1^(+-1),...,x_d^(+-1)]))`       `(FPC3)`

is the coefficient-`p` congruence kernel and

`J=SL_3(Z)`                                              `(FPC4)`

is the constant lower-right block on coordinates `3,4,5`.  Moreover,

`|J/(J intersect L_n)|=|SL_3(F_p)|`                     `(FPC5)`

for every `n`.  Thus the degree of the Kazhdan transfer cover is one fixed
number while the Laurent quotient size tends to infinity.

The marked radical word

`w=i_2(h)i_1(h)^(-1)`, `h=e_12(x_1^(-1))`              `(FPC6)`

has infinite order in the abelianizations of both limiting intermediate
subgroups

`pi^(-1)(E(p))` and `pi^(-1)(J E(p))`.                  `(FPC7)`

It follows that the integral filling norms of `w` diverge in both finite
cover towers.  Since the transfer degree is constant, there is no remaining
square-root degree loss.  Precisely one of the following occurs after
passing to a subsequence:

1. the minimum real filling norms diverge, which proves FALSE by the real
   filling escape theorem; or
2. the real filling norms stay bounded and the canonical integral
   discriminant radii diverge in both towers.

This is stronger than abstract relative separability of `J`: it exhibits a
single-prime tower with an exactly computed limit subgroup and an exactly
constant averaging degree.  The second branch still requires a nonzero
marked paired-discriminant estimate; integral escape by itself is not a
FALSE certificate.

## 2. The fixed-prime Laurent quotients

Use

`R=Z[x_1^(+-1),...,x_d^(+-1)]`,
`R_bar=F_p[x_1^(+-1),...,x_d^(+-1)]`,
`E=EL_r(R)`,                                            `(FPC8)`

and write

`F=G *_E G ~= E semidirect_varphi L`,
`L=Q*Q`, `Q=SL_d(Z)`,                                  `(FPC9)`

where `varphi:L->Q` is the fold action on Laurent exponents.  Let

`red_p:E->EL_r(R_bar)`                                  `(FPC10)`

be coefficient reduction and define `E(p)` by `(FPC3)`.

Choose integers

`2<=M_1 | M_2 | M_3 | ...`, `M_n->infinity`;           `(FPC11)`

for example `M_n=(n+1)!`.  Put

`U_n=(Z/M_n Z)^d`, `A_n=F_p[U_n]`.                     `(FPC12)`

Sending `x_i` to the `i`-th standard group element of `U_n` gives a
`Q`-equivariant finite ring quotient

`ev_n:R->A_n`.                                         `(FPC13)`

It induces a homomorphism of `F` into a finite semidirect product; denote
its kernel by `N_n`.  Because `M_n|M_(n+1)`, the quotient
`U_(n+1)->U_n` makes these maps compatible, so

`N_1>=N_2>=...`.                                       `(FPC14)`

Only their restriction to `E` will matter.

**Lemma 1 (fixed-prime detection).**

`intersection_n(N_n intersect E)=E(p)`.                `(FPC15)`

**Proof.**  Inclusion `E(p)<=N_n intersect E` is immediate.  Conversely,
write an element of `E` as its matrix over `R` and suppose that its image is
the identity over every `A_n`.  After coefficient reduction, every matrix
entry off the diagonal and every diagonal entry minus one is a Laurent
polynomial over `F_p` killed by all maps

`R_bar->F_p[(Z/M_n Z)^d]`.                             `(FPC16)`

A nonzero Laurent polynomial has finite exponent support.  For all
sufficiently large `M_n`, its distinct exponents remain distinct modulo
`M_n`; their group elements are linearly independent in the group-algebra
basis.  Hence it cannot map to zero.  Every entry in `(FPC16)` is therefore
zero, so the original matrix lies in `E(p)`.  End proof.

Choose a nested residual chain

`T_1>=T_2>=... normal L`, `intersection_nT_n=1`,        `(FPC17)`

and let `pr:F->L` be the semidirect-product projection.  Define

`L_n=N_n intersect pr^(-1)(T_n)`.                      `(FPC18)`

The `L_n` are nested normal finite-index subgroups of `F`.

**Theorem 2 (exact kernel limit).**

`intersection_nL_n=E(p)`.                              `(FPC19)`

**Proof.**  Write `f=e ell` with `e in E` and `ell in L`.  If `f` belongs
to every `L_n`, then `(FPC17)--(FPC18)` give `ell=1`; Lemma 1 then gives
`e in E(p)`.  The reverse inclusion follows directly from the definitions.
End proof.

The extra residual factor in `(FPC18)` is load-bearing.  The finite Laurent
quotients alone see the `L`-coordinate only through the fold action and
would retain `ker(varphi)` in their intersection.

## 3. Exact relative limit and exact degree

Let

`J=diag(I_2,SL_3(Z),I_(r-5))<=E`.                      `(FPC20)`

Its image under every fixed-prime Laurent quotient is the same constant
block

`J_bar=diag(I_2,SL_3(F_p),I_(r-5))`.                   `(FPC21)`

Reduction `SL_3(Z)->SL_3(F_p)` is onto, since the elementary matrices
generate `SL_3(F_p)`.  Therefore

`J intersect L_n=ker(J->SL_3(F_p))=:J(p)`              `(FPC22)`

for every `n`; the projection factor in `(FPC18)` is trivial on `J`.  This
proves `(FPC5)`.

**Theorem 3 (exact relative limit).**

`intersection_n J L_n=J E(p)`.                         `(FPC23)`

**Proof.**  The inclusion from right to left is immediate from
`E(p)<=L_n`.  Conversely, let `f` belong to every `J L_n`.  Projecting to
`L` and using `(FPC17)` shows that `f=e in E`.  For every `n`, membership
`e in J L_n` says that the image of `e` in the `n`-th Laurent quotient is
a constant matrix in `J_bar`.

Reduce the entries of `e` modulo `p`.  Every entry outside the block in
`(FPC21)` differs from the corresponding identity entry by a Laurent
polynomial killed in all sufficiently large group-algebra quotients, hence
is zero by the argument of Lemma 1.  Inside the block, every nonconstant
Laurent coefficient is likewise killed in all sufficiently large
quotients, hence is zero.  Thus `red_p(e)` itself lies in `J_bar`.

Choose `j in J` lifting this constant matrix.  Then `j^(-1)e in E(p)`, so
`e in J E(p)`.  End proof.

Equivalently, the relative limit consists exactly of those Laurent
elementary matrices whose coefficient-`p` reduction is a constant
lower-right `SL_3(F_p)` block.

## 4. The radical word survives both limit groups

Let

`Gamma=EL_r(Z[x_1,...,x_d])`,
`h=e_12(x_1^(-1)) in E-Gamma`.                         `(FPC24)`

**Lemma 4.**

`h notin E(p) Gamma` and `h notin J E(p) Gamma`.        `(FPC25)`

**Proof.**  It is enough to prove the second assertion.  Suppose
`h=b gamma` with `b in J E(p)` and `gamma in Gamma`.  Reduce modulo `p`.
The matrix `red_p(b)` is supported on the constant block with coordinates
`3,4,5`, so it and its inverse leave the first two rows unchanged.  Hence

`red_p(gamma)=red_p(b)^(-1)red_p(h)`                   `(FPC26)`

has `(1,2)` entry `x_1^(-1)`.  But every entry of the reduction of an
element of `Gamma` belongs to the polynomial subring
`F_p[x_1,...,x_d]`, which does not contain `x_1^(-1)`.  Contradiction.
The first assertion follows from `E(p)<=J E(p)`.  End proof.

Use the fold extension

`1->R_0->D=G *_Gamma G -> F=G *_E G->1`.              `(FPC27)`

For every subgroup `B<=E`, the first vertex copy of `E` splits the preimage:

`pi^(-1)(B)=R_0 semidirect B`.                         `(FPC28)`

The split-homology theorem in
`FALSE_INTERMEDIATE_SPLIT_HOMOLOGY.md` says that if `h notin B Gamma`,
then `w` has infinite order in the abelianization of `(FPC28)`.  Lemma 4
therefore gives:

**Corollary 5.**  The word `w` has infinite order in both groups in
`(FPC7)`.

## 5. Constant-degree filling escape

Pull the finite-index subgroups back to `D`:

`K_n=pi^(-1)(L_n)`, `H_n=pi^(-1)(J L_n)`.             `(FPC29)`

They are nested, contain `w`, and

`intersection_nK_n=pi^(-1)(E(p))`,
`intersection_nH_n=pi^(-1)(J E(p))`.                  `(FPC30)`

The finite-index radical theorem gives

`w in [K_n,K_n] intersect [H_n,H_n]`                  `(FPC31)`

at every finite stage.  Corollary 5 and integral filling compactness then
give

`Fill_Z,2(w;K_n)->infinity`,
`Fill_Z,2(w;H_n)->infinity`.                           `(FPC32)`

The cover `Y_(K_n)->Y_(H_n)` is regular of the constant degree

`m=|SL_3(F_p)|`.                                      `(FPC33)`

The exact transfer identities and the Kazhdan orbit-average decoder give

`Fill_R(w;K_n)^2`
` =m^(-1)Fill_R(w;H_n)^2+epsilon_n^2`,
`0<=epsilon_n<=C`,                                    `(FPC34)`

and

`rho_(K_n)(c_(K_n))^2`
` >=m^(-1)rho_(H_n)(c_(H_n))^2-C^2`.                 `(FPC35)`

Integral pushdown also gives directly

`Fill_Z(w;K_n)^2>=m^(-1)Fill_Z(w;H_n)^2`.             `(FPC36)`

Thus the former `sqrt(m_n)` rate problem disappears completely.

**Theorem 6 (fixed-prime dichotomy).**  Along a subsequence, either

`Fill_R(w;K_n)->infinity` and Fill_R(w;H_n)->infinity`, `(FPC37)`

in which case a hyperlinear nonsofic group exists, or both real filling
sequences are bounded and

`rho_(K_n)(c_(K_n))->infinity`,
`rho_(H_n)(c_(H_n))->infinity`.                        `(FPC38)`

**Proof.**  By `(FPC34)`, one real sequence is unbounded exactly when the
other is, after passing to a subsequence.  Unbounded real filling proves
FALSE by `FALSE_REAL_FILLING_ESCAPE_DICHOTOMY.md`.  Otherwise use the exact
integral discriminant Pythagoras

`Fill_Z^2=Fill_R^2+rho(c)^2`                           `(FPC39)`

in each tower together with `(FPC32)`.  End proof.

## 6. What remains in the discriminant branch

The fixed-prime tower proves that integral escape is not being diluted by
a growing stabilizer image.  It does **not** turn `(FPC38)` into marked
discriminant divergence automatically.  A large shortest representative of
the canonical cycle class can be orthogonal modulo `Z` to every canonical
word class, or can lie in a totally isotropic subgroup of the discriminant
pairing.

The exact remaining target is therefore one of the following.

1. Prove `(FPC37)` by estimating the invariant transfer filling in the
   fixed-prime quotient.
2. In branch `(FPC38)`, produce points `y_n` for which the marked numerator
   in `(MDD20)` grows faster than the nearest paired-discriminant well.
3. Prove a nonisotropy statement for the canonical filling classes and a
   correlated low-carry/high-word tail.  Uniform subgroup averaging cannot
   do this in regular covers by
   `FALSE_REGULAR_COVER_MEAN_ENERGY_NO_GO.md`.

The main structural advance is exact: the transfer loss is a fixed constant
`sqrt(|SL_3(F_p)|)`, so any genuine unbounded real or marked-discriminant
quantity downstairs remains unbounded upstairs.
