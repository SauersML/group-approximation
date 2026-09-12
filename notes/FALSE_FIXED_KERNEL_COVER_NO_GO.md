# Fixed-kernel covers have zero relative filling class

Date: 2026-08-11

## 1. Outcome

The large regular covers obtained in
`FALSE_EXPLICIT_FP_RADICAL_DOUBLE.md` by pulling back finite quotients of
`SL_d(Z)*SL_d(Z)` cannot support the modular transfer-holonomy
construction.  More generally, suppose a family of presentation covers
factors through one quotient

`pi:H->Q`,  `K=ker(pi)`,

and the marked word satisfies

`w in [K,K]`.                                                     `(FKC1)`

Then the relative transferred-filling class from
`FALSE_TRANSFERRED_FILLING_PAIRING_FORMULA.md` vanishes on every cover in
the family:

`kappa_(w,X)=0 in K_1/S(K_X)`.                                   `(FKC2)`

Consequently every transferable holonomy is only the fixed ordinary
integral filling functional.  Its centered size is at most a fixed constant
times the norm of the base cycle, so neither the amplified holonomy
criterion nor the marked discriminant-divergence criterion can fire on
such a family.

For the explicit polynomial/Laurent double, the kernel of

`D -> SL_d(Z)*SL_d(Z)`

contains both perfect Laurent elementary vertex subgroups.  The radical
word is a product of one element from each of them, hence lies in the
commutator subgroup of that fixed kernel.  The entire quotient-only tower
is therefore sterile.  Any viable finite-cover construction must retain a
nontrivial finite image of the Laurent elementary subgroup.

## 2. Fixed-kernel filling lemma

Let

`H=<S|R>`                                                         `(FKC3)`

be finitely presented, let `P` be its presentation complex, and let
`pi:H->Q` be a quotient with kernel `K`.  Let `P_K->P` be the corresponding
connected cover.  Fix a word `w` satisfying `(FKC1)`.

Consider any connected regular finite presentation cover `P_X->P` whose
action factors through `Q`.  Equivalently, its stabilizer `L` is a normal
finite-index subgroup of `H` satisfying

`K<=L`.                                                          `(FKC4)`

Write

`A_X:C^1(P_X,Z)->C^2(P_X,Z)`,
`K_X=ker(A_X^*)`,  `K_1=ker(A_1^*)`,                              `(FKC5)`

and let `S:C^2(P_X,Z)->C^2(P,Z)` be cellular pushforward, or coordinate
sum.

**Theorem 1 (fixed-kernel filling).**  There is one integral base filling

`A_1^*z_0=b_w`                                                   `(FKC6)`

such that for every cover satisfying `(FKC4)` and every vertex `x` there
is an integral lifted filling

`A_X^*z_(w,x)=b_(w,x)`                                           `(FKC7)`

with

`S z_(w,x)=z_0`.                                                  `(FKC8)`

In particular `(FKC2)` holds.

**Proof.**  The cellular first homology of `P_K` is the abelianization of
`K`.  Assumption `(FKC1)` therefore says that the lifted cellular cycle
`b_(w,K)` is zero in `H_1(P_K,Z)`.  Choose a finite integral cellular
two-chain `z_K` with

`partial z_K=b_(w,K)`.                                           `(FKC9)`

The inclusion `(FKC4)` gives a covering map

`P_K -> P_L=P_X`.                                                 `(FKC10)`

Push `z_K` first to `P_X` and then to `P`.  Call the two resulting chains
`z_(w,x_0)` and `z_0`, where `x_0` is the vertex represented by `L`.
Cellular naturality proves `(FKC6)--(FKC7)`, and functoriality of
pushforward proves

`S z_(w,x_0)=z_0`.                                                `(FKC11)`

For any other vertex `x`, translate `z_(w,x_0)` by a deck
transformation.  Its boundary is `b_(w,x)`, while coordinate sum is deck
invariant.  Thus `(FKC8)` holds for every vertex.

By definition,

`kappa_tilde_(w,X,x)=S z_(w,x)-z_0`.                              `(FKC12)`

Equation `(FKC8)` makes this representative zero, proving `(FKC2)`.  End
proof.

The same proof works for nonregular finite covers after restricting to the
chosen base vertex.  Regularity is used here only to obtain the identical
statement at every vertex.

## 3. Holonomy consequence

Suppose `v in K_1`, `q>1`, and the modular transfer equation

`A_X a=Jv mod q`                                                  `(FKC13)`

is solvable.  The paired filling formula and `(FKC2)` give

`Hol_(w,X,q)(Jv)=<v,z_0> mod q`.                                  `(FKC14)`

Hence

`H_q(Hol_(w,X,q)(Jv))<=|<v,z_0>|<=||z_0||_2 ||v||_2`.             `(FKC15)`

The quotient in the amplified hypothesis is therefore uniformly bounded:

`H_q(Hol_(w,X,q)(Jv))/||v||_2<=||z_0||_2`.                        `(FKC16)`

This remains true when both `v` and `q` vary.  Thus Theorem 3a of
`FALSE_TRANSFER_HOLONOMY_CERTIFICATE.md` cannot apply.  In the compatible
profinite formulation, `(FKC14)` says that the radical transgression is the
diagonal ordinary integer `<v,z_0>`, never a nonintegral profinite integer.

The same fixed diagram controls every phase class, not only constant-lift
classes.  Let `C_D` be the number of relator-cell occurrences in the chosen
diagram, counted with multiplicity.  For an arbitrary circle-valued edge
phase table `theta`, let `A_X theta` be its relator residual and let
`B_(w,X)theta` be its vector of marked word phases.  The lifted chain
identity `(FKC7)--(FKC8)` gives at every vertex

`(B_(w,X)theta)_x=<A_X theta,z_(w,x)> mod Z`.                     `(FKC16a)`

The chains `z_(w,x)` are deck translates of one fixed finite pattern.
The triangle inequality on `R/Z`, followed by the finite convolution
inequality on the deck group, yields

`||dist(B_(w,X)theta,Z)||_2`
` <=C_D ||dist(A_X theta,Z)||_2`.                                `(FKC16b)`

Thus the marked circle Lipschitz ratios satisfy

`Lambda_(w,X)<=C_D`                                               `(FKC16c)`

uniformly over the entire fixed-kernel family.  By the exact comparison in
`TRUE_EXACT_COVER_MONOMIAL_DISCRIMINANT.md`, the corresponding monomial
character-domination constants are uniformly bounded as well.  Hence the
marked discriminant-divergence criterion and its tensor amplification also
cannot fire on this family.

## 4. Application to the explicit radical double

Use the notation of `FALSE_EXPLICIT_FP_RADICAL_DOUBLE.md`:

`D=G *_Gamma G`,  `G=E semidirect Q`,  `Q=SL_d(Z)`,               `(FKC17)`

and

`w=i_2(h)i_1(h)^(-1)`,  `h=e_12(x_1^(-1)) in E`.                  `(FKC18)`

Let

`pi:D->Q*Q`                                                       `(FKC19)`

be the quotient which kills the two vertex copies `E_1,E_2` of `E`, and
put `K=ker(pi)`.  Stable elementary groups are perfect, so

`E_i=[E_i,E_i]<= [K,K]` for `i=1,2`.                              `(FKC20)`

Both factors in `(FKC18)` belong to `[K,K]`; consequently

`w in [K,K]`.                                                     `(FKC21)`

Theorem 1 now applies to every finite quotient pulled back through
`(FKC19)`.  In particular, arbitrarily large cover degree in the free
product quotient does not create any marked torsion: the relative filling
class is identically zero at every one of those stages.

Every finite quotient of `D` kills its sofic radical and hence factors
through

`G *_E G ~= E semidirect (Q*Q)`.                                  `(FKC22)`

The conclusion does not say that all finite covers of `D` are sterile.  It
says that a live cover must use a finite quotient of `(FKC22)` whose
restriction to `E` is nontrivial.  Congruence quotients of the Laurent
coefficient ring, together with a compatible finite quotient of the
substitution action, are therefore load bearing; quotienting only the
`Q*Q` coordinate can never work.

## 5. Scope

The hypothesis `w in [K,K]` is stronger than `w in K`.  The latter merely
makes the lifted word a loop; it does not provide one filling in the fixed
intermediate cover.  This distinction is exactly where a surviving marked
class can live.  In the full radical quotient `(FKC22)`, the kernel of
`D->G *_E G` is free by its free action on the Bass--Serre tree and need not
be perfect.  Finite quotients which retain part of `E` can therefore still
have a nonzero relative filling class.  The theorem isolates that remaining
case without claiming it is nonempty.
