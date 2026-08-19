# A fully framed radical element has amenable conjugacy stabilizer

Date: 2026-08-12

## 1. Outcome

There is a residually finite Kazhdan infranormal pair

`Gamma<G`                                                `(FAC1)`

and an element

`h in normalClosure_G(Gamma)\Gamma`                     `(FAC2)`

such that its **full conjugacy stabilizer**

`C_G(h)`                                                 `(FAC3)`

is amenable.  Consequently the actual conjugacy-orbit action

`G curvearrowright {g h g^(-1):g in G}`
`             ~= G/C_G(h)`                              `(FAC4)`

is a sofic action.

For the symmetric double

`D=G *_Gamma G`, `w=i_2(h)i_1(h)^(-1)`,                 `(FAC5)`

amalgam normal form and the Kun--Thom radical theorem give

`1!=w in Rad_sof(D)`.                                    `(FAC6)`

This strengthens the monomial-frame construction in
`FALSE_AMENABLE_MONOMIAL_FRAME_KUN_THOM_PAIR.md`.  There only the external
monomial orbit had amenable stabilizer.  Here the matrix frame also kills
the nonamenable stabilizer coming from elementary conjugation.  Thus the
real transition system needed by the FALSE route now has sofic Schreier
charts.  The remaining problem is no longer construction of those charts;
it is the matrix-valued relation/fiber assignment over them.

## 2. The pair

Let

`A=Z directSum J`, `J=Z epsilon_1 directSum Z epsilon_2`
`                    directSum Z epsilon_3`, `J^2=0`.    `(FAC7)`

Let

`Lambda=M_(3 times 2)(Z)~=Z^6`, `Lambda_+=N^6`,         `(FAC8)`

and let `L=SL_3(Z)` act on `Lambda` by left multiplication on both
columns.  It acts trivially on `A`.  Put

`B_+=Z[Lambda_+]`, `B=Z[Lambda]`,

`R_+=A[Lambda_+]=B_+ directSum (B_+ tensor J)`,

`R=A[Lambda]=B directSum (B tensor J)`.                 `(FAC9)`

Define

`Gamma=E_4(R_+)`,

`G=E_4(R) semidirect L`.                                `(FAC10)`

**Theorem 1.**  The groups in `(FAC10)` are residually finite Kazhdan
groups.  The subgroup `Gamma<G` is infranormal and nonnormal, and

`N:=normalClosure_G(Gamma)=E_4(R)=ker(G->L)`.            `(FAC11)`

**Proof.**  The rings `R_+` and `R` are finitely generated commutative
unital rings.  Universal-lattice property `(T)` gives property `(T)` for
their elementary groups.  The quotient `L` has property `(T)`, so extension
stability gives property `(T)` for `G`.

Every positive elementary matrix `I+e_ij in L` preserves `Lambda_+` and
therefore compresses `Gamma` into itself.  These positive transvections
generate `L` as a group.  The `L`-conjugates of `B_+` generate `B`: positive
coordinate monomials already lie in `B_+`, and a determinant-one diagonal
sign matrix sends any chosen row coordinate to its negative, producing the
corresponding inverse monomial.  Elementary additivity and

`[e_ij(a),e_jk(b)]=e_ik(ab)`                             `(FAC12)`

then show that the conjugates of `E_4(R_+)` generate `E_4(R)`.  Hence the
compression semigroup

`{g in G:g Gamma g^(-1)<=Gamma}`                        `(FAC13)`

generates `G`; this is infranormality.  It also proves `(FAC11)`.
Nonnormality follows from the explicit strict predecessor in Section 3.

Both rings are residually finite: reduce the integer coefficients modulo a
prime and the exponent lattice modulo `m Lambda`.  The resulting finite
ring quotients separate their elements.  Matrix reduction separates
`E_4(R_+)` and `E_4(R)`, while finite congruence quotients separate `L`.
This proves residual finiteness of both semidirect factors.  End proof.

## 3. The three-tag strict predecessor

In `M_4(Z)` put

`P=diag(1,-1,1,-1)`,                                    `(FAC14)`

`S=e_12+e_23+e_34+e_41`, `E=e_12`.                     `(FAC15)`

Thus `P` is invertible and traceless, `S` is the cyclic permutation matrix,
and `E` is one directed edge of that cycle.  Form the square-zero matrix
frame

`X=epsilon_1 P+epsilon_2 S+epsilon_3 E in M_4(J)`.      `(FAC16)`

As in the monomial-frame construction, set

`t=I+e_12 in L`,

`v=(e_1,e_2-e_1) in Lambda`, `u=t v=(e_1,e_2)`.         `(FAC17)`

Then `u in Lambda_+` but `v notin Lambda_+`.  Define

`gamma=1+y^u X in Gamma`,

`h=t^(-1) gamma t=1+y^v X in E_4(R)\Gamma`.            `(FAC18)`

Here the displayed membership is literal.  Because all products of the
`epsilon_i` vanish,

`1+y^z X=(1+epsilon_1 y^z P)`
`          (1+epsilon_2 y^z S)(1+epsilon_3 y^z E)`.    `(FAC19)`

The last factor is elementary.  The middle factor is the product of the
four root transvections belonging to the four summands of `S`; all cross
terms vanish.  Finally `1+epsilon_1 y^z P` is a direct sum of two blocks

`diag(1+a,1-a)`, `a=epsilon_1 y^z`, `a^2=0`,           `(FAC20)`

and each block is elementary by the standard factorization of
`diag(r,r^(-1))` with `r=1+a`.  Thus `(FAC18)` lies in the stated elementary
groups.  The negative entry of `v` proves `h notin Gamma` and proves that
the inclusion is nonnormal.

## 4. The matrix frame has scalar commutant

**Lemma 2.**  Over every commutative ring `K`, the common commutant of `S`
and `E` in `M_4(K)` consists of scalar matrices.

**Proof.**  Since `S^4=1`, the unital algebra generated by `S` and `E`
contains

`S^j E S^(-j)`, `j=0,1,2,3`.                           `(FAC21)`

These are the four directed matrix units around the cycle

`1->2->3->4->1`.                                       `(FAC22)`

Products along directed paths give every matrix unit `e_ij`, including the
diagonal units.  Hence `S` and `E` generate `M_4(K)` as a unital algebra.
A matrix commuting with both therefore commutes with every matrix unit and
is scalar.  End proof.

The role of the third tag is important.  The invertible tag `P` detects the
Laurent exponent by determinant, while the pair `(S,E)` makes the internal
matrix commutant scalar.  A single scalar tag would instead be fixed by all
elementary conjugations and would retain the full nonamenable base
stabilizer.

## 5. The full stabilizer is amenable

Let

`I=B tensor J`,                                         `(FAC23)`

the square-zero ideal in `R=B directSum I`, and let

`K=ker(E_4(R)->E_4(B))`.                                `(FAC24)`

Every member of `K` is a matrix `1+Z` with entries of `Z` in `I`.  Since
`I^2=0`, multiplication in `K` is addition of the matrices `Z`.  In
particular,

`K is abelian`.                                         `(FAC25)`

The external stabilizer of the ordered frame `v` is

`H_*=Stab_L(v)`
`   ={I+a e_13+b e_23:a,b in Z}~=Z^2`.                 `(FAC26)`

**Theorem 3 (amenable full conjugacy stabilizer).**

`C_G(h)` is amenable.                                   `(FAC27)`

**Proof.**  Let `(g,l) in E_4(R) semidirect L` centralize `h`, and let
`g_0 in E_4(B)` be the reduction of `g` modulo `I`.  Conjugation of a
square-zero matrix depends only on this reduction.  Comparing the three
independent tags in `(FAC16)` gives

`y^(l v) g_0 P g_0^(-1)=y^v P`,

`y^(l v) g_0 S g_0^(-1)=y^v S`,

`y^(l v) g_0 E g_0^(-1)=y^v E`.                        `(FAC28)`

Take determinants in the first equality.  Since `det(P)=1` and the Laurent
ring `B=Z[Lambda]` is a domain,

`y^(4 l v)=y^(4v)`, hence `l v=v`.                      `(FAC29)`

Thus `l in H_*`, and `(FAC28)` says that `g_0` commutes with `P,S,E`.
Lemma 2 shows that `g_0=b I_4` is scalar.  Since `g_0 in E_4(B)` has
determinant one, `b^4=1`.  The only torsion units of the integral Laurent
ring are `+-1`, so the possible scalar reductions form a finite group.

Therefore reduction gives an exact sequence

`1 -> C_G(h) intersect K -> C_G(h)`
`  -> subgroup of ({+-I_4} times H_*)`.                `(FAC30)`

The kernel is abelian by `(FAC25)`, and the group on the right is amenable
by `(FAC26)`.  Amenability is closed under subgroups and extensions, proving
`(FAC27)`.  End proof.

## 6. The real conjugacy orbit has sofic Schreier charts

The conjugacy orbit of `h` is canonically the homogeneous `G`-set

`Orb_G(h)~=G/C_G(h)`.                                   `(FAC31)`

The group `G` is residually finite, hence sofic, and Theorem 3 gives an
amenable point stabilizer.  The amenable-stabilizer theorem for sofic
actions therefore yields:

**Corollary 4.**  The action `G curvearrowright Orb_G(h)` is sofic.  For
every fixed finite group window and finite orbit window it admits finite
root-dependent injective Schreier charts whose equivariance defect tends to
zero.

This is the actual induced transition system asked for in the FALSE
program.  It includes both elementary conjugation and the external
`SL_3(Z)` transport.  No global scalar transversal and no primitive
three-moment test is asserted; those are ruled out by the property-`(T)`
holonomy no-go.  The charts here are the root-dependent charts permitted by
the amenable-stabilizer theorem.

## 7. The radical word

Use `(FAC11)` and form the double and marked word in `(FAC5)`.  Because

`h in N\Gamma`,                                        `(FAC32)`

amalgam normal form gives `w!=1`.  Its image becomes trivial in

`G *_N G`,                                              `(FAC33)`

and the Kun--Thom theorem for the Kazhdan infranormal pair identifies the
kernel of the quotient to `(FAC33)` with the sofic radical.  This proves
`(FAC6)`.

## 8. What remains for FALSE

The previous monomial-frame endgame needed two different finite systems:

1. amenable external charts for `L/Stab_L(v)`; and
2. a still-missing way to handle the nonamenable elementary base
   stabilizer.

The three-tag frame replaces both by the single genuine action `(FAC31)`.
Thus the base-stabilizer mismatch is gone.

The remaining gate is a finite relation-module extension theorem:

> On the root-dependent Schreier charts for `G/C_G(h)`, assign paired
> finite-dimensional fibers so that every fixed elementary Steinberg and
> semidirect covariance relation has normalized Hilbert--Schmidt defect
> tending to zero, the two sectors agree on the `Gamma` window, and the
> marked conjugacy label retains a uniform gap.

The orbit labels are actual conjugates of `h`, so they satisfy linear
relations inside the finite-rank square-zero matrix module.  Corollary 4
solves their finite transport but does not automatically preserve those
additive relations.  That relation-module compatibility is now the sole
analytic obstruction in this framed route.

The required conclusion here is **tracial**, not merely operator-norm MF.
More precisely, suppose the extension theorem produces maps

`phi_(i,n):G -> U(k_n)`, `i=0,1`,                       `(FAC34)`

which are asymptotic homomorphisms in normalized Hilbert--Schmidt norm and
satisfy

`||phi_(0,n)(gamma)-phi_(1,n)(gamma)||_2 -> 0`          `(FAC35)`

for every `gamma in Gamma`, while

`liminf_n ||phi_(1,n)(h)phi_(0,n)(h)^(-1)-1||_2 > 0`.  `(FAC36)`

Then the two limiting homomorphisms into the tracial matrix ultraproduct
agree on `Gamma`.  The universal property gives a homomorphism

`Psi:D=G *_Gamma G -> product_omega U(k_n)`             `(FAC37)`

whose image is hyperlinear and in which
`w=i_2(h)i_1(h)^(-1)` survives.  If `im(Psi)` were sofic, the quotient map
from `D` to `im(Psi)` would kill `w in Rad_sof(D)`, a contradiction.
Therefore `im(Psi)` is hyperlinear and nonsofic.  Neither faithfulness of
`Psi` nor faithfulness of either vertex map is required.

Shulman's amalgamated-MF criterion would separately give an operator-norm
MF conclusion from compatible norm-corona embeddings.  That conclusion is
not the endpoint above: group MF in Shulman's operator-norm sense does not
imply hyperlinearity, because operator-norm visibility can be supported on
vanishing normalized rank.  Thus no MF-to-hyperlinear implication is used
in `(FAC34)--(FAC37)`.

## Reference

David Gao, Gregory Patchell, and Srivatsav Kunnawalkam Elayavalli,
*Sofic actions on graphs*, arXiv:2408.15470, Theorem 2.20 and Lemma 2.18.
