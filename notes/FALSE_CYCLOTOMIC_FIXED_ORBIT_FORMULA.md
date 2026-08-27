# Cyclotomic relation torsion is fixed-double-coset excess

Date: 2026-08-11

## 1. Outcome

This note computes the part of the fixed-prime cyclotomic sector coming
from the Bass--Serre relation module

`M=ker(Z[F/Gamma]->Z[F/E])`.                           `(CFO1)`

Let

`F=E semidirect L`, `L=Q*Q`,
`Gamma<=E`,
`E_p=ker(E->EL_r(R/pR))`,
`B_p=<E_p,h>`, `B_p/E_p=C_p`,                          `(CFO2)`

where `h=e_12(x_1^(-1))`.  Write `O_p=Z[zeta_p]` and let `chi` be the
nontrivial cyclotomic character of `B_p/E_p`.

There are three exact conclusions.

1. The module `M` splits over the quotient coordinate `ell in L` as

   `M=directSum_(ell in L) Aug_Z(E/Gamma_ell)`,
   `Gamma_ell=ell Gamma ell^(-1)`.                     `(CFO3)`

2. For any `B_p`-set `X`, the visible cyclotomic quotient of
   `Aug_Z(X)` has one copy of `F_p` for every **excess fixed orbit** of the
   induced `C_p`-action on `E_p\X`.  More precisely, if `s` is the number
   of fixed orbits, its fixed-orbit torsion quotient is

   `F_p^(s-1)` for `s>=1`.                             `(CFO4)`

   The only additional term is an explicit cokernel of stabilizer-homology
   maps.

3. For every `ell in L`, the `C_p`-set

   `E_p\E/Gamma_ell`                                  `(CFO5)`

   has infinitely many fixed points.  They are represented by diagonal
   Laurent matrices whose conjugation moves the exponent `-e_1` into the
   polynomial cone defining `Gamma_ell`.

Thus the unknown complementary sector from
`FALSE_PRIME_TWO_BOCKSTEIN_IDENTIFICATION.md` is not diffuse or
hypothetical.  It contains an explicit infinite fixed-double-coset excess
in every `L`-fiber.  A complete simultaneous-Bockstein computation must
show that these differences are killed by ordinary-liftable cylinders, or
exhibit one difference surviving the stabilizer transgression and then
prove its marked visibility.

## 2. Fiberwise decomposition of the relation module

Because `E normal F` and `F/E=L`, the map of permutation modules in
`(CFO1)` preserves the `L`-coordinate.  For `ell in L`, put

`Gamma_ell=ell Gamma ell^(-1)<=E`.                     `(CFO6)`

The fiber of `F/Gamma->F/E` over `ell E` identifies with

`E/Gamma_ell`.                                        `(CFO7)`

Indeed, writing elements in the form `e ell`, one has

`e_1 ell Gamma=e_2 ell Gamma`
` iff e_2^(-1)e_1 in ell Gamma ell^(-1)`.              `(CFO8)`

On this fiber the map `Z[F/Gamma]->Z[F/E]` is ordinary augmentation.
Taking kernels independently in every fiber proves `(CFO3)` as a
`Z[B_p]`-module decomposition.  Notice that `B_p<=E`, so it does not mix
the fibers.

## 3. Twisted homology of one orbit

We first record a general calculation.  Let a group `B` admit a quotient

`eta:B->C_p`,                                          `(CFO9)`

and let `O_chi` be the cyclotomic right `Z[B]`-module.  If `H<=B`, Shapiro
and degree-zero homology give

`O_chi tensor_(Z[B]) Z[B/H]`
` ~=O_p/<chi(h)-1:h in H>`.                            `(CFO10)`

Since `p` is prime, this is

`O_p` if `eta(H)=1`,
`F_p=O_p/varpi` if `eta(H)=C_p`.                       `(CFO11)`

The first case will be called a free-type orbit and the second a
fixed-type orbit.  Equivalently, after first quotienting a `B`-set by
`ker(eta)`, the corresponding `C_p`-orbit has size `p` or `1`.

Let

`X=disjointUnion_(a in A) B/H_a`                      `(CFO12)`

be a `B`-set and put `I_X=Aug_Z(X)`.  Tensor the exact sequence

`0->I_X->Z[X]->Z->0`                                  `(CFO13)`

with `O_chi`.  Shapiro gives the exact segment

`directSum_a H_1(H_a,O_chi|H_a) -> H_1(B,O_chi)`
` -> (I_X)_chi -> directSum_a H_0(H_a,O_chi)`
` -> H_0(B,O_chi) ->0`.                               `(CFO14)`

Here `(I_X)_chi=O_chi tensor_(Z[B]) I_X` and
`H_0(B,O_chi)=F_p`.  Define

`C_X^chi=coker(directSum_a H_1(H_a,O_chi|H_a)`
`                    ->H_1(B,O_chi))`.                `(CFO15)`

Then `(CFO14)` becomes the short exact sequence

`0->C_X^chi->(I_X)_chi->K_X^chi->0`,                  `(CFO16)`

where `K_X^chi` is the kernel of the last degree-zero map.

Suppose there are `r` free-type and `s` fixed-type orbits.  Equations
`(CFO10)--(CFO11)` identify the last map with

`O_p^(r) directSum F_p^(s) ->F_p`,                    `(CFO17)`

the sum of reductions modulo `varpi` on the `O_p` coordinates and the
identity on the `F_p` coordinates.

**Theorem 1 (fixed-orbit formula).**  The degree-zero quotient in
`(CFO16)` is

`K_X^chi ~= O_p^(r)` if `s=0`,
`K_X^chi ~= O_p^(r) directSum F_p^(s-1)` if `s>=1`.    `(CFO18)`

The same formula holds for infinite orbit sets, with direct sums.

**Proof.**  If `s=0`, choose one `O_p` coordinate.  The condition that the
sum lie in `varpi O_p` determines that coordinate as

`varpi c-sum(other coordinates)`,                     `(CFO19)`

leaving `r` free `O_p` parameters.  If `s>=1`, choose one `F_p`
coordinate.  It is uniquely determined by all `O_p` coordinates and the
remaining `s-1` fixed coordinates, giving the second line of `(CFO18)`.
The same coordinate elimination respects finite support.  End proof.

The summand `F_p^(s-1)` is the exact fixed-orbit excess.  Sequence
`(CFO16)` is load bearing: without controlling `C_X^chi`, a torsion
quotient of `K_X^chi` must not automatically be called a direct summand of
the whole module.  When two fixed points are represented by points of `X`
which are themselves fixed by a lift of the generator, however, their
difference is an actual `varpi`-torsion element of `(I_X)_chi` mapping to
the corresponding nonzero difference in `(CFO18)`.

For comparison, ordinary coefficients give

`directSum_a H_1(H_a,Z)->H_1(B,Z)->(I_X)_B`
` ->Z^(A)->Z->0`.                                     `(CFO20)`

Thus all torsion in `(I_X)_B` lies in the explicit stabilizer cokernel

`coker(directSum_a (H_a)_ab->B_ab)`.                  `(CFO21)`

The degree-zero fixed-orbit differences themselves are free integrally.
This is the algebraic reason the cyclotomic excess can be canceled by an
ordinary lift even though it is primary in the twisted sector.

## 4. Fixed double cosets in every Laurent fiber

Let `A=varphi(ell) in SL_d(Z)` be the exponent action of `ell`.  The
coefficient ring defining `Gamma_ell` is the semigroup ring on the pointed
cone

`A N^d <= Z^d`.                                       `(CFO22)`

Let `n_0 in {0,1}^d` be the unique parity vector satisfying

`A n_0=-e_1 mod 2`.                                   `(CFO23)`

For every `m in N^d`, put

`n_m=n_0+2m`,
`v_m=(A n_m+e_1)/2 in Z^d`,                           `(CFO24)`

and let

`d_m=diag(x^(-v_m),x^(v_m),1,...,1) in E`.            `(CFO25)`

The diagonal matrix lies in the elementary group in stable rank: for every
unit `u`, `diag(u,u^(-1),1,...)` is a standard product of elementary
matrices.

Direct conjugation gives

`d_m^(-1) h d_m=e_12(x^(-e_1+2v_m))`
`                 =e_12(x^(A n_m)) in Gamma_ell`.     `(CFO26)`

Hence `h` fixes the point `d_m Gamma_ell in E/Gamma_ell` exactly.  In
particular the double coset

`E_p d_m Gamma_ell in E_p\E/Gamma_ell`                `(CFO27)`

is a fixed point of the residual `C_p`-action.

**Theorem 2 (infinitely many fixed double cosets).**  As `m` varies in a
suitable infinite ray in `N^d`, the points `(CFO27)` are pairwise distinct.
Consequently every fiber in `(CFO3)` has infinitely many fixed-type
`B_p`-orbits and its quotient `(CFO18)` contains

`directSum_N F_p`.                                    `(CFO28)`

**Proof.**  Suppose `(CFO27)` is the same for `m,m'`.  Reducing modulo `p`
gives

`d_(m')^(-1)d_m in EL_r(F_p[A N^d])`.                 `(CFO29)`

The first two diagonal entries of the left side are inverse Laurent
monomials with exponent `v_m-v_(m')`.  Both can belong to the semigroup
ring in `(CFO29)` only if

`v_m-v_(m') in A N^d` and
`v_(m')-v_m in A N^d`.                                `(CFO30)`

The cone `A R_+^d` is pointed, so `(CFO30)` forces `v_m=v_(m')`.  Along a
ray on which `A m` is nonzero, `(CFO24)` then forces `m=m'`.  End proof.

One may avoid any appeal to units of the elementary group in `(CFO29)`:
membership in `EL_r(F_p[A N^d])` already implies entrywise membership in
that semigroup ring, which is all `(CFO30)` uses.

## 5. Application to the Bass--Serre relation module

Apply Theorem 1 to each summand in `(CFO3)`.  The fixed representatives
`d_m Gamma_ell` are fixed by `h` itself, not merely after passing to
`E_p`-double cosets.  Therefore, for `m!=m'`,

`delta_(d_m Gamma_ell)-delta_(d_(m') Gamma_ell)`       `(CFO31)`

is fixed by `h`.  Its class in twisted coinvariants is killed by `varpi`,
and its nonzero image in `(CFO18)` proves that the class itself is nonzero.

**Corollary 3 (explicit relation-module cyclotomic torsion).**  For every
`ell in L`, the cyclotomic coinvariants of the relation summand
`Aug_Z(E/Gamma_ell)` contain an explicit subspace

`directSum_N F_p`,                                    `(CFO32)`

generated by the differences `(CFO31)`.

This complements the lower-right congruence classes in
`FALSE_CONGRUENCE_TORSION_TORUS_CANCELLATION.md`.  Those classes lie in the
base group `B_p`; `(CFO31)` lies in the Bass--Serre relation module.

## 6. Common-lift fixed orbits cancel already in the free fold kernel

There is an exact group-level cancellation for the explicit family
`(CFO31)`.  The quotient of the Bass--Serre tree by `R_0` is obtained from
the Bass--Serre tree of `F=G *_E G` by replacing every edge `ell E` by the
parallel-edge set `E/Gamma_ell`.  Choose one base edge `o` in a fiber.
For another edge `x` in that fiber, the two-edge loop

`a_x=x o^(-1)`                                         `(CFO33)`

represents an element of the free group `R_0`, with homology class
`delta_x-delta_o`.

**Lemma 4 (parallel-edge common-lift lemma).**  Suppose an element `b in
B_p` fixes two distinct parallel edges `x,y`.  Then the free-kernel element

`k_(x,y)=a_x a_y^(-1) in R_0`                         `(CFO34)`

is nontrivial and is fixed by conjugation by `b`.

**Proof.**  Put `q=bo`.  Since `b` fixes the two endpoints of the edge
fiber and fixes `x,y`, its action on the loops `(CFO33)` is

`b a_x b^(-1)=x q^(-1)=a_x a_q^(-1)`,
`b a_y b^(-1)=y q^(-1)=a_y a_q^(-1)`.                 `(CFO35)`

Therefore

`b k_(x,y)b^(-1)`
` =(a_x a_q^(-1))(a_y a_q^(-1))^(-1)`
` =a_x a_y^(-1)=k_(x,y)`.                             `(CFO36)`

The loop is reduced and nontrivial when `x!=y`; equivalently its
abelianization is `delta_x-delta_y!=0`.  End proof.

The section `B_p->H_p=R_0 semidirect B_p` has trivial intersection with
`R_0`.  Hence `b` and `k_(x,y)` generate a copy of `Z^2` whenever `b` has
infinite order.  In particular this holds for `b=h` and the diagonal fixed
edges `(CFO25)`.

Let `alpha_(x,y)` be the mod-`p` fundamental class of that torus.  The same
calculation as `(CTC29)` gives

`beta_1(alpha_(x,y))=0`,
`beta_chi(alpha_(x,y))=unit*[k_(x,y)]`.                `(CFO37)`

**Theorem 5 (explicit fixed-orbit excess cancels).**  Every class generated
by the differences `(CFO31)` belongs to

`beta_chi(ker(beta_1))`.                               `(CFO38)`

Consequently the entire explicit `directSum_N F_p` in `(CFO32)` is zero in
the simultaneous Bockstein quotient.

**Proof.**  The diagonal representatives `(CFO25)` are all fixed by the
same element `h`, by `(CFO26)`.  Apply Lemma 4 and `(CFO37)` to every pair.
End proof.

As in the root-torus calculation, these group-homology torus classes lift
to the cellular `H_2` of any presentation cover with fundamental group
`H_p`.  The Hopf map is onto in degree two, degree-one homology agrees, and
the Bocksteins are natural.  Hence Theorem 5 cancels the actual
finite-support cellular classes used in the filling problem.

This identifies the first genuinely possible fixed-orbit obstruction.  A
general fixed point of `E_p\E/Gamma_ell` supplies an element

`b_x=e_x h in B_p`, `e_x in E_p`,                    `(CFO39)`

which fixes a representative edge.  Two fixed orbits cancel by Lemma 4 if
their stabilizing lifts can be chosen equal.  The residual classes are
therefore indexed by the failure to conjugate the lifts `(CFO39)` to one
common lift using `E_p`; equivalently they are controlled by the relevant
nonabelian `C_p`-cocycle set of `E_p`.  Merely counting fixed points greatly
overcounts the live simultaneous obstruction.

## 7. General fixed-orbit tori cancel after abelianizing the fold kernel

Let

`H_p=R_0 semidirect B_p`                               `(CFO40)`

be the split intermediate group and recall that `(R_0)_ab=M`.  Its
metabelian quotient is

`Hbar_p=M semidirect B_p`.                             `(CFO41)`

Let `y in M` be any class fixed by `h`; in particular one may take a
difference `(CFO31)`.  In `Hbar_p`, the elements `(y,1)` and `(0,h)`
commute.  Let

`alpha_y^bar in H_2(Hbar_p,F_p)`                       `(CFO42)`

be their torus fundamental class.

Exactly the cellular calculation of `(CTC29)` gives

`beta_1(alpha_y^bar)=0`,
`beta_chi(alpha_y^bar)=unit*y`.                        `(CFO43)`

Here the second class is interpreted in the cyclotomic `H_1` of the
metabelian quotient.

**Theorem 6 (metabelian cancellation and derived remainder).**  In the
metabelian group `Hbar_p`, every fixed class `y` contributes zero to the
simultaneous Bockstein quotient.  Upstairs in `H_p`, suppose first that the
torus class `alpha_y^bar` belongs to the image of

`H_2(H_p,F_p)->H_2(Hbar_p,F_p)`.                       `(CFO44)`

Then the cyclotomic class of `y` belongs to

`beta_chi(ker(beta_1))`
` +ker(H_1(H_p,O_chi)->H_1(Hbar_p,O_chi)).`             `(CFO45)`

If `(CFO44)` fails, its obstruction, and the kernel in `(CFO45)`, are both
controlled by the same derived module `(CFO49)` below.

**Proof.**  Formula `(CFO43)` itself proves cancellation in `Hbar_p`.
Now choose a preimage `alpha_y` in `(CFO44)`.  Naturality gives

`q_* beta_1(alpha_y)=0`,
`q_* beta_chi(alpha_y)=unit*y`,                        `(CFO46)`

where `q:H_p->Hbar_p`.  The ordinary map

`H_1(H_p,Z)->H_1(Hbar_p,Z)`                            `(CFO47)`

is an isomorphism: its kernel `[R_0,R_0]` already lies in the commutator
subgroup of `H_p`.  Hence `beta_1(alpha_y)=0`.  The second equality in
`(CFO46)` says exactly that `unit*y-beta_chi(alpha_y)` belongs to the
cyclotomic kernel in `(CFO45)`.  This proves the displayed containment.
End proof.

The obstruction to `(CFO44)` has a precise home.  Apply the homology
five-term sequence to

`1->[R_0,R_0]->H_p->Hbar_p->1`.                       `(CFO48)`

It contains

`H_2(H_p,F_p)->H_2(Hbar_p,F_p)`
` ->H_1([R_0,R_0],F_p)_(Hbar_p)`.                      `(CFO49)`

With cyclotomic integral coefficients, the same sequence contains

`H_1([R_0,R_0],O_p)_(Hbar_p)`
` ->H_1(H_p,O_chi)->H_1(Hbar_p,O_chi)->0`.             `(CFO50)`

Consequently a fixed-orbit torus can fail to cancel only when its
transgression is nonzero in

`([R_0,R_0]_ab tensor F_p)_(Hbar_p)`,                  `(CFO51)`

or when the lifted cancellation differs from `y` by the image of the
integral version of the same derived coinvariant module in `(CFO50)`.

This is the exact derived remainder.  Merely finding many fixed double
cosets or much cyclotomic `H_1` torsion is insufficient: all of it cancels
in the metabelian quotient, and only data from `[R_0,R_0]_ab` can survive
upstairs.

The apparent commutator module has a simpler description.  The fold kernel
`R_0` is free because it acts freely on the Bass--Serre tree.  Put
`M=(R_0)_ab`.  Conjugation by the normal subgroup `M<=Hbar_p` on
`[R_0,R_0]_ab` imposes the quotient

`[R_0,R_0]/[R_0,[R_0,R_0]]`.                          `(CFO52)`

The commutator subgroup of `[R_0,R_0]` lies in the third lower-central
subgroup and is already killed in `(CFO52)`.  The classical degree-two
free-group calculation therefore gives

`([R_0,R_0]_ab)_M`
` ~=gamma_2(R_0)/gamma_3(R_0)`
` ~=exterior^2 M`.                                    `(CFO53)`

Taking the remaining `B_p`-coinvariants yields:

**Theorem 7 (exterior-square derived target).**  The mod-`p` target in
`(CFO49)` is naturally

`H_1([R_0,R_0],F_p)_(Hbar_p)`
` ~=(exterior^2 M tensor F_p)_(B_p)`.                  `(CFO54)`

With cyclotomic coefficients, the source controlling the kernel in
`(CFO50)` is the corresponding twisted module

`(exterior^2 M tensor O_chi)_(B_p)`.                  `(CFO55)`

**Proof.**  Coinvariants by `M` are precisely conjugation coinvariants by
`R_0`.  They divide `[R_0,R_0]_ab` further by
`[R_0,[R_0,R_0]]`, giving `(CFO52)`.  For a free group, the commutator map

`u wedge v |->[u_tilde,v_tilde]`                      `(CFO56)`

is the standard isomorphism from `exterior^2 M` to
`gamma_2/gamma_3`.  Tensor with the coefficient ring and then take the
remaining `B_p`-coinvariants.  End proof.

Thus the live derived calculation is exterior-quadratic in the already
known permutation kernel `M`; it does not require a basis of the free group
`[R_0,R_0]`.

## 8. The exact surviving quotient

Equations `(CFO15)--(CFO18)` identify everything still hidden by the phrase
"other relation-module sector."  For the fiber `ell`, it consists of:

1. the fixed-orbit excess generated by `(CFO31)`; and
2. the stabilizer-homology cokernel

   `C_ell^chi`
   `=coker(directSum_(B_p-orbits) H_1(H_a,O_chi|H_a)`
   `              ->H_1(B_p,O_chi))`.                 `(CFO57)`

The congruence-root subspace of the target in `(CFO57)` is already canceled
by commuting tori, by `(CTC30)`.  Therefore the next local theorem should
be formulated as follows:

> Show that every difference `(CFO31)` is the cyclotomic Bockstein of a
> mod-`p` cylinder class which lifts ordinarily, equivalently that its
> entire derived remainder in `(CFO54)--(CFO55)` vanishes, and show that
> the residual cokernel `(CFO57)` is generated by the same root-torus
> classes.

If both assertions hold, then

`ker(beta_1)+ker(beta_chi)=H_2(Y;F_p)`                `(CFO58)`

for the finite-support sector and the primary-gluing escape is eliminated.
If either assertion fails, `(CFO31)` and `(CFO57)` give explicit finite
generators for the surviving class; the problem is then to prove that its
moving finite-cover cancellations have unbounded marked incidence.

No vanishing is claimed in this note.  Its contribution is an exact orbit
formula, an explicit infinite family of candidate classes, and the
exterior-square targets `(CFO54)--(CFO55)` which measure whether those
classes are genuine or automatically canceling.

## 9. First-order arithmetic of a non-common stabilizing lift

The phrase "nonabelian cocycle" in Section 6 has a concrete first
congruence approximation.  Put

`Rbar=R/pR`,
`Pbar_ell=F_p[A N^d]`, `A=varphi(ell)`.                `(CFO59)`

Let `gbar Gamma_bar_ell` be a fixed point of the `hbar`-action on
`Ebar/Gamma_bar_ell`.  Thus

`gamma_bar=gbar^(-1) hbar gbar in Gamma_bar_ell`.      `(CFO60)`

Choose lifts `g in E` and `gamma in Gamma_ell`.  There is a unique
first-congruence error `Delta mod p` defined by

`g^(-1) h g gamma^(-1)=1+p Delta mod p^2`.             `(CFO61)`

It belongs to `sl_r(Rbar)` by the determinant-one calculation of Lemma 1
in the congruence-torsion note.

Changing the lift of the edge by `e in E_p` on the left and changing the
polynomial lift by an element of `Gamma_ell intersect E_p` changes `Delta`
by

`Delta |-> Delta+(Ad(gbar^(-1))(Ad(hbar)-1))X`
`             -Ad(gamma_bar)Y`,                       `(CFO62)`

where `X in sl_r(Rbar)` and `Y in sl_r(Pbar_ell)` are their first
congruence logarithms.

Since `gamma_bar=gbar^(-1)hbar gbar`, the first variable in `(CFO62)`
runs through

`(Ad(gamma_bar)-1)sl_r(Rbar)`.                         `(CFO63)`

The first congruence images here are the full displayed Lie algebras.
Off-diagonal matrices come from `e_ij(pf)`, and diagonal differences come
from their commutators with constant opposite-root elements.  Conjugation
by `gamma_bar in EL_r(Pbar_ell)` preserves the polynomial
matrix algebra `sl_r(Pbar_ell)`.  Hence the invariant obstruction space is

`Def(gbar)`
` =sl_r(Rbar)/((Ad(gamma_bar)-1)sl_r(Rbar)`
`                 +sl_r(Pbar_ell)).`                  `(CFO64)`

**Theorem 8 (first-order common-lift criterion).**  The class

`obs_1(gbar)=[Delta] in Def(gbar)`                     `(CFO65)`

is independent of all choices in `(CFO61)`.  It vanishes if and only if
the fixed mod-`p` double coset has a representative fixed by `h` modulo
`p^2`, after changing the representative by `E_p` and the edge stabilizer
element by the level-`p` polynomial congruence subgroup.

**Proof.**  Formula `(CFO62)` follows by expanding

`(eg)^(-1)h(eg)`                                       `(CFO66)`

modulo `p^2` and moving the right polynomial correction past `gamma`.
Equations `(CFO63)--(CFO64)` show that all choices change `Delta` by the stated
denominator.  Conversely, a solution of the linear equation saying that
`A` lies in that denominator supplies `X,Y` for which the corrected error
in `(CFO61)` is zero modulo `p^2`.  End proof.

For the diagonal fixed points `(CFO25)`, one may choose the exact equality
`d_m^(-1)h d_m in Gamma_ell`, so `Delta=0` and `(CFO65)` vanishes.  A genuinely
wild fixed orbit must have a nonzero obstruction at some congruence depth;
`(CFO64)` is its first possible occurrence.

This quotient is computable by sparse Laurent support.  For example, when
`gamma_bar` is a root transvection, `Ad(gamma_bar)-1` changes only the
corresponding row and column, while `sl_r(Pbar_ell)` removes the polynomial
cone.  The remaining coordinates are negative-cone root directions.  The
lower-right part is already known to cancel through `(CTC30)`; the live
first-order search should therefore project `(CFO64)` further by the
commuting-root-torus subspace before testing the exterior-square
transgression `(CFO54)`.

Vanishing of `(CFO65)` is only a lift modulo `p^2`.  An exact integral
common lift requires compatible vanishing at all higher congruence depths;
no Hensel or algebraization assertion is made here.

## 10. A quadratic repair warning at the next congruence depth

A naive iteration of Theorem 8 can report a false higher-depth obstruction
if one quotients only by the new linear correction and forgets quadratic
terms coming from homogeneous solutions at the preceding depth.  The
following exact example is a useful regression test.

Work in one Laurent variable, at `p=2`, in the upper-left `3 x 3` block.
Put

`g=e_21(x)e_12(x^(-1))e_21(x^(-2))`,
`h=e_12(x^(-1))`.                                      `(CFO68)`

Direct multiplication gives

`g^(-1)h g=`
` [[3+4x^(-3),       4x^(-1), 0],`
`  [-x-4x^(-2)-4x^(-5), -1-4x^(-3),0],`
`  [0,0,1]].`                                           `(CFO69)`

Modulo two this is the polynomial transvection `e_21(x)`, and modulo four
all negative Laurent terms vanish.  Looking only at the next linearized
error therefore suggests a nonzero negative class.  Nevertheless define

`c=[[1-2x^(-3), -2x^(-1),0],`
`   [2x^(-5),    1+2x^(-3),0],`
`   [0,0,1]].`                                          `(CFO70)`

There is an exact elementary factorization

`c=e_12(-x^2)e_21(2x^(-5))e_12(x^2)`,                 `(CFO71)`

so `c in E_2`: its reduction modulo two is the identity.  Another direct
multiplication gives

`c^(-1)g^(-1)h g c=e_21(-x) in Gamma`.                `(CFO72)`

Equivalently, with `a=g c g^(-1) in E_2`, the representative `a g=g c`
of the same `E_2`-double coset is fixed by `h` exactly.

The mechanism is a finite Bezout correction.  The rank-one factorization
of `(CFO69)-1` is

`u=(2x^(-1),-1-2x^(-3),0)^T`,`
`v=(x+2x^(-2),2,0)`, `v u=0`.                          `(CFO73)`

The first column of `(CFO70)` solves the Laurent Bezout equation which
removes the negative part of `v`, while the second column restores
determinant one.  Formula `(CFO71)` shows that this is an allowed relative
elementary correction, not merely a matrix in the ambient general linear
group.

Thus a genuine all-depth obstruction must be invariant under the full
nonlinear torsor of lower-depth solutions.  Reapplying `(CFO64)` at each
depth with one arbitrarily chosen lift is insufficient.  The bounded exact
search in `experiments/wild_fixed_coset_search.py` should consequently be
used only as a first-order falsification tool.
