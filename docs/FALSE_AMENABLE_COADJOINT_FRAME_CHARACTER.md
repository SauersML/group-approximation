# The framed radical element has an amenable coadjoint character orbit

Date: 2026-08-12

## 1. Outcome

The three-tag construction in
`FALSE_FULLY_FRAMED_AMENABLE_CONJUGACY_ORBIT.md` also solves the dual
stabilizer problem.  The square-zero kernel `K` has a character `chi_theta`
such that

1. `chi_theta(h)!=1` for the marked strict predecessor `h`;
2. the stabilizer of `chi_theta` in the whole reductive/external group is
   amenable; and
3. the corresponding induced representation is an honest monomial
   representation of the entire vertex group, so every additive tangent
   relation is satisfied exactly.

The irrational phase in the definition of `chi_theta` is essential.  A
finite-order character would be fixed by a nonamenable congruence kernel.
The irrational character detects equality of integral functionals and
removes that kernel.

Thus the remaining relation-module gate has been reduced again.  There is
no longer a need to assign phases independently to linearly dependent
conjugacy labels: one exact character does it functorially.  What is still
missing is a paired finite approximation which repeats its rooted marked
visibility on positive density while the two sectors agree on `Gamma`.

## 2. Split square-zero form of the vertex group

Retain the notation of the fully framed construction:

`R=B directSum I`,

`B=Z[Lambda]`, `I=B tensor J`, `I^2=0`,               `(ACF1)`

and

`G=E_4(R) semidirect L`, `L=SL_3(Z)`.                 `(ACF2)`

Reduction modulo `I` has the ring section `B->R`.  Hence

`E_4(R)=K semidirect E_4(B)`,                          `(ACF3)`

where

`K=ker(E_4(R)->E_4(B))`                               `(ACF4)`

is abelian.  Put

`H=E_4(B) semidirect L`.                               `(ACF5)`

Then

`G=K semidirect H`.                                    `(ACF6)`

Every element of `K` has the form

`1+Z`, `Z=sum_(j=1)^3 epsilon_j Z_j`,                 `(ACF7)`

with `Z_j in M_4(B)` and `tr(Z_j)=0`.  Conversely the elementary
square-zero factorizations show that these traceless tangent matrices lie
in the relative elementary kernel.  Multiplication is

`(1+Z)(1+Z')=1+Z+Z'`.                                  `(ACF8)`

## 3. An integral constant-term pairing

For `f in B`, write `CT(f)` for its coefficient at the zero exponent.  The
bilinear form

`<Y,Z>=CT tr(YZ)`, `Y,Z in M_4(B)`,                    `(ACF9)`

is integral and nondegenerate modulo scalar matrices on the traceless
submodule.  More precisely, if `<Y,Z>=0` for every traceless `Z`, then `Y`
is scalar.  This follows by testing against off-diagonal matrix units and
diagonal differences, with arbitrary Laurent-monomial coefficients.

The form is invariant in the required contragredient sense.  For
`g in E_4(B)` and `l in L`, cyclicity of matrix trace and invariance of the
constant coefficient under `l` give

`<Y,l^(-1)(g^(-1) Z g)>=<g l(Y) g^(-1),Z>`.           `(ACF10)`

Thus the coadjoint action on the representing matrix `Y` is the same
conjugation/external action as the primal tangent action.

## 4. The irrational framed character

Recall

`v=(e_1,e_2-e_1) in Lambda`,                           `(ACF11)`

and the three traceless matrices

`P=diag(1,-1,1,-1)`,

`S=e_12+e_23+e_34+e_41`, `E=e_12`.                    `(ACF12)`

Define the dual frame

`Y_1=y^(-v)P`, `Y_2=y^(-v)S`, `Y_3=y^(-v)E`.          `(ACF13)`

Choose `theta in R\Q` and define

`chi_theta(1+Z)`
` =exp(2 pi i theta sum_(j=1)^3 CT tr(Y_j Z_j)).`     `(ACF14)`

Equation `(ACF8)` makes this a character of the abelian group `K`.

For the marked tangent

`h=1+y^v(epsilon_1P+epsilon_2S+epsilon_3E)`,           `(ACF15)`

one has

`sum_j CT tr(Y_j y^v X_j)`
` =tr(P^2)+tr(S^2)+tr(E^2)=4`.                         `(ACF16)`

Consequently

`chi_theta(h)=exp(8 pi i theta)!=1`.                   `(ACF17)`

## 5. Exact amenable coadjoint stabilizer

Let

`H_chi=Stab_H(chi_theta)`.                              `(ACF18)`

**Theorem 1.**  The group `H_chi` is amenable.  More precisely, its image
under the evident coordinates is contained in

`{+-I_4} times Stab_L(v)`,

`Stab_L(v)={I+a e_13+b e_23:a,b in Z}~=Z^2`.          `(ACF19)`

**Proof.**  Suppose `(g,l) in H` fixes `chi_theta`.  Since all values of
the functional in `(ACF14)` are integers and `theta` is irrational,
equality of the circle characters implies equality of the underlying
integral linear functionals.  By `(ACF9)--(ACF10)`, for each `j`,

`g l(Y_j) g^(-1)-Y_j`                                  `(ACF20)`

annihilates every traceless matrix and is therefore scalar.  Both terms in
`(ACF20)` are traceless.  The Laurent ring is torsion-free, so taking trace
shows that the scalar is zero.  Hence

`g l(Y_j) g^(-1)=Y_j`, `j=1,2,3`.                     `(ACF21)`

Apply determinants to the `P` equality.  Since `P` is invertible,

`y^(-4lv)=y^(-4v)`,                                    `(ACF22)`

and torsion-freeness of `Lambda` gives `lv=v`.  Thus `l` belongs to the
abelian group in `(ACF19)`.  The remaining equalities say that `g` commutes
with `P,S,E`.  The matrices `S,E` generate all matrix units, as proved in
the fully framed note, so `g` is scalar.  Its determinant is one; the only
torsion units of `Z[Lambda]` are `+-1`.  This proves `(ACF19)` and hence
amenability.  End proof.

**Why irrationality matters.**  If `(ACF14)` were replaced by a character
of order `p`, then every element of the level-`p` congruence kernel in
`E_4(B)` would fix it.  That kernel is nonamenable.  Irrationality upgrades
circle equality back to equality of integral functionals and is exactly
what makes Theorem 1 true.

## 6. Exact monomial representation

The character `chi_theta` is invariant under `H_chi`, so it extends to a
character of the amenable subgroup

`S_chi=K semidirect H_chi`                             `(ACF23)`

by

`tilde_chi(k,a)=chi_theta(k)`.                         `(ACF24)`

Induce it to `G`:

`Pi_theta=Ind_(S_chi)^G(tilde_chi)`.                   `(ACF25)`

On `ell^2(H/H_chi)`, this is the explicit monomial representation

`Pi_theta(k) delta_(xH_chi)`
` =chi_theta(x^(-1) k x) delta_(xH_chi)`,              `(ACF26)`

while `H` acts by the left quasi-regular permutations.  In particular,

`<Pi_theta(h)delta_(H_chi),delta_(H_chi)>`
` =chi_theta(h)!=1`.                                   `(ACF27)`

This construction resolves an important ambiguity in the earlier finite
fiber proposal.  The phase assigned to every conjugate tangent label is
not chosen separately: it is evaluation by the single character
`chi_theta`.  Therefore every integral linear relation in `K`, every
square-zero addition relation, and every semidirect covariance relation is
satisfied exactly by `(ACF26)`.

Because `H` is residually finite and `H_chi` is amenable, the homogeneous
action

`H curvearrowright H/H_chi`                            `(ACF28)`

is sofic by the amenable-stabilizer theorem.  Hence the actual transition
system of the monomial representation has finite root-dependent Schreier
charts.  The stabilizer phases needed on any fixed window form only a
finite subset of the amenable group `H_chi`.

There is an important normalized-trace limitation.  The restriction of
`Pi_theta` to `H` is the quasi-regular representation on `H/H_chi`.  This
is an infinite transitive orbit.  Since `H` has property `(T)`,
`FALSE_COADJOINT_INDUCTION_KAZHDAN_TRACE_NO_GO.md` proves that for a fixed
Kazhdan pair `(S,kappa)` and every trace-one density operator `rho`,

`max_(s in S)`
` ||Pi_theta(s)sqrt(rho)-sqrt(rho)Pi_theta(s)||_(HS)>=kappa.` `(ACF29)`

Thus direct finite-rank compression of the exact induced representation
cannot supply tracial matrix models.  The sofic orbit charts remain useful
because they are root-dependent; they must be coupled to two nonliftable
relative-holonomy fields rather than glued into one global compression.

## 7. Exact remaining gate

Equation `(ACF27)` is **rooted** visibility, not yet normalized-trace
visibility.  A single distinguished orbit coordinate may have density zero
in growing finite models.  One must combine `(ACF26)` with the paired
cyclic/Fourier amplifier so that the marked phase is repeated on positive
density, while the two resulting models agree asymptotically on the
positive subgroup `Gamma`.

The quantitative gap `(ACF29)` also rules out a superficially simpler
amplification: taking larger finite-rank corners of `(ACF26)` and repeating
them.  At least one fixed external Kazhdan relation then has order-one
tracial defect.  Hence the word **paired** in the remaining theorem is
load bearing.

The remaining theorem can now be stated without any independent phase
variables:

> Construct paired finite amplifications of the one exact character orbit
> `(ACF26)` on the sofic charts `(ACF28)` such that their restrictions to
> every fixed `Gamma` window converge in normalized Hilbert--Schmidt norm,
> while the normalized squared displacement of `h` stays bounded below.

All additive tangent and base-conjugation relations are already exact
before truncation.  Only positive-density amplification and paired
agreement remain.  A proof would give compatible tracial models of the two
vertex copies in the radical double and therefore a hyperlinear nonsofic
quotient.

## Reference

David Gao, Gregory Patchell, and Srivatsav Kunnawalkam Elayavalli,
*Sofic actions on graphs*, arXiv:2408.15470, Theorem 2.20 and Lemma 2.18.
