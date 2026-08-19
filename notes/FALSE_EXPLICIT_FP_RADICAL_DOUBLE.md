# An explicit finitely presented radical double with large finite covers

Date: 2026-08-11

## 1. Purpose

`FALSE_RADICAL_FILLING_DISCRIMINANT.md` invoked finite-presentation
localization before applying its cover calculations to the Kun--Thom
symmetric double.  That loses the arithmetic structure of the original
pair.  In a stable integral polynomial/Laurent version of the pair, no
localization is necessary: the double itself is finitely presented, its
sofic radical has the already computed fold-kernel description, and it has
an explicit quotient with arbitrarily large finite quotients.

This supplies a concrete source presentation and cover tower for the
modular transfer-holonomy certificate in
`FALSE_TRANSFER_HOLONOMY_CERTIFICATE.md`.

**Closure update.**  The presentation and radical calculation below remain
valid, but the proposed `Q*Q` cover tower is now ruled out for modular
holonomy.  `FALSE_FIXED_KERNEL_COVER_NO_GO.md` observes that the marked word
lies in the commutator subgroup of the fixed kernel of `D->Q*Q`.  One
commutator filling in that intermediate cover therefore pushes compatibly
to every cover in this family.  Its relative filling class is zero and its
holonomy ratio is uniformly bounded.  Sections 5--6 document the candidate
closed by that no-go; they are no longer a live FALSE target.

## 2. The stable integral pair

Fix `d>=3` and put

`R_+=Z[x_1,...,x_d]`,
`R=Z[x_1^(+-1),...,x_d^(+-1)]`.                                    `(FPRD1)`

Choose the elementary rank `r` in a standard stable range for both rings.
For example, `r>=d+4` is a safe dimension-based choice for the standard
stability input used here.  In particular choose it large enough that

`K_2(r,R_+)=K_2(R_+)`, `K_2(r,R)=K_2(R)`.                          `(FPRD2)`

Set

`Gamma=EL_r(R_+)`, `E=EL_r(R)`,
`Q=SL_d(Z)`, `G=E semidirect Q`,                                   `(FPRD3)`

where `Q` acts on Laurent monomials by its natural action on exponent
vectors.

The integral-coefficient Kun--Thom theorem recorded in `NOTEPAD.md` proves:

1. `Gamma` and `G` are residually finite Kazhdan groups;
2. `Gamma<G` is infranormal and nonnormal; and
3. its normal closure in `G` is

   `N=normalClosure_G(Gamma)=E`.                                    `(FPRD4)`

The last equality follows because `Q`-conjugates of the positive elementary
root elements produce every Laurent monomial root element.

## 3. Finite presentability

**Theorem 1.**  In the stable range `(FPRD2)`, each of `Gamma`, `E`, `G`,
and

`D=G *_Gamma G`                                                    `(FPRD5)`

is finitely presented.

**Proof.**  The rings in `(FPRD1)` are finitely generated commutative
unital rings.  Allcock's finite-presentation theorem for spherical
Steinberg groups over finitely generated rings gives finite presentations
of

`St_r(R_+)`, `St_r(R)`.                                             `(FPRD6)`

Because `Z` is regular, Quillen homotopy invariance and the iterated
Bass--Heller--Swan fundamental theorem give

`K_2(R_+)~=K_2(Z)`,                                                 `(FPRD7)`

`K_2(R)~=K_2(Z)`
` directSum d K_1(Z)`
` directSum binom(d,2) K_0(Z)`.                                    `(FPRD8)`

Here `K_0(Z)=Z`, `K_1(Z)={+-1}`, and `K_2(Z)=Z/2`.  Thus both groups
in `(FPRD7)--(FPRD8)` are finitely generated.  Stability `(FPRD2)`
identifies them with the central kernels of

`St_r(R_+)->EL_r(R_+)`, `St_r(R)->EL_r(R)`.                         `(FPRD9)`

Quotienting a finitely presented group by the normal closure of finitely
many elements preserves finite presentability.  Hence `Gamma` and `E` are
finitely presented.

The arithmetic group `Q` is finitely presented.  A semidirect product of
two finitely presented groups is finitely presented once the action of a
finite generating set of the acting group on a finite generating set of the
normal group is written down.  Therefore `G=E semidirect Q` is finitely
presented.  Finally `Gamma` is finitely generated, so the standard
amalgamated presentation of two copies of `G` over `Gamma` is finite.
This proves finite presentability of `D`.  End proof.

The stable-rank choice is load bearing.  It avoids the unstable `K_2`
finite-generation issue for the rank-five binary Leavitt elementary group;
no assertion about that open unstable kernel is used here.

The cited inputs can be checked independently of the Kun--Thom argument:
Allcock, *Steinberg groups as amalgams*, Theorem 1.4 supplies the finite
Steinberg presentations, while the usual dimension stable range and the
fundamental theorem of algebraic `K`-theory supply `(FPRD2)` and
`(FPRD7)--(FPRD8)`.

## 4. Explicit radical and explicit word

The complete-radical theorem for a Kun--Thom symmetric double gives

`Rad_sof(D)=ker(D -> G *_N G)`.                                    `(FPRD10)`

Using `(FPRD4)`, this becomes

`Rad_sof(D)=ker(D -> G *_E G)`.                                    `(FPRD11)`

Choose

`t=diag(-1,-1,1,...,1) in Q`,
`gamma=e_12(x_1) in Gamma`,                                        `(FPRD12)`

and put

`h=t gamma t^(-1)=e_12(x_1^(-1)) in E setminus Gamma`.             `(FPRD13)`

If `i_1,i_2:G->D` are the two vertex embeddings, define

`w=i_2(h)i_1(h)^(-1)`.                                             `(FPRD14)`

**Proposition 2.**  The word `w` is a nontrivial explicit element of
`Rad_sof(D)`.

**Proof.**  Since `h in N=E`, equation `(FPRD10)` puts `w` in the radical.
The normal-form theorem for the amalgamated free product says that
`i_2(h)i_1(h)^(-1)` is nontrivial whenever `h notin Gamma`, which is
`(FPRD13)`.  End proof.

Thus `(FPRD5)` is a concrete finitely presented nonsofic group with a fixed
length-two radical witness.  Unlike the quasisimple Leavitt--Steinberg
group, it also has many nontrivial finite quotients.

## 5. Large regular finite covers, and why the quotient-only tower is sterile

Quotient each vertex group `G` by `E`.  Since `Gamma<=E`, the universal
property of the amalgam gives a surjection

`pi:D -> Q*Q`.                                                      `(FPRD15)`

The group `Q=SL_d(Z)` is infinite and residually finite, and the free product of
residually finite groups is residually finite.  It is infinite and finitely
generated, so it has finite quotients of unbounded order.  Pulling those
quotients back through `(FPRD15)` gives connected regular finite covers of
the fixed finite presentation `(FPRD5)` of unbounded degree.  The word `w`
lies in every corresponding subgroup, as it already lies in the kernel of
`(FPRD15)`.

Consequently all objects in the transfer-holonomy theorem are explicit:

1. the fixed finite presentation is the stable amalgamated presentation of
   `(FPRD5)`;
2. the radical word is `(FPRD14)`;
3. the regular covers come from congruence/free-product quotients of
   `Q*Q`; and
4. the finite test is

   `A_X a=Jv mod q`,
`   <a,b_(w,x)>/q bounded away from Z`.                              `(FPRD16)`

If a sequence satisfies `(FPRD16)` with `||v||/q->0`, Theorem 3 of
`FALSE_TRANSFER_HOLONOMY_CERTIFICATE.md` produces a hyperlinear nonsofic
group.

However, the particular covers obtained only from `(FPRD15)` cannot satisfy
the amplified marked-holonomy condition.  Let `K=ker(pi)`.  It contains the
two vertex copies `E_1,E_2` of the perfect group `E`, and

`w=i_2(h)i_1(h)^(-1) in [K,K]`.                                    `(FPRD17)`

The fixed-kernel filling theorem in
`FALSE_FIXED_KERNEL_COVER_NO_GO.md` therefore gives

`kappa_(w,X)=0`                                                    `(FPRD18)`

on every finite cover pulled back through `(FPRD15)`.  Its holonomy is only
the fixed ordinary integral filling functional and satisfies

`H_q(Hol(Jv))<=C||v||`                                             `(FPRD19)`

with one presentation-dependent constant `C`.  Thus increasing the order
of a quotient of `Q*Q` alone is rigorously sterile.

## 6. Closed arithmetic task

The originally proposed finite computation was:

> Along finite quotients of
> `G *_E G ~= E semidirect (SL_d(Z)*SL_d(Z))` whose restriction to `E` is
> nontrivial, determine the largest modulus for which a constant base
> two-cycle becomes a modular coboundary, and evaluate one solution on the
> parallel-edge loop `(FPRD14)`.

The transfer subgroup `S(K_X)<=K_1`, the maximal divisibility modulus, and
the radical holonomy all live in fixed rank.  The full cover cycle lattice
and its enormous discriminant basis are unnecessary.  The degree-holonomy
congruence `(THC29)` says in advance that only prime powers shared with the
cover degree can contribute.  Equations `(FPRD17)--(FPRD19)` add a stronger
screen: the quotient must retain nontrivial Laurent elementary data.  The
convenient `Q*Q` tower proves that large covers exist, but cannot itself
produce radical holonomy.

The perfect-kernel theorem is stronger than this screen.  With its fixed
kernel commutator filling `z_0`, every solution satisfies

`Hol_(w,X,q)(Jv)=<v,z_0> mod q`,
`H_q(Hol_(w,X,q)(Jv))/||v||<=||z_0||`.                            `(FPRD17)`

Thus the requested centered growth cannot occur, for any choice of
modulus or base cycle.  A replacement explicit tower must not factor
through one quotient whose kernel contains `w` in its commutator subgroup.
