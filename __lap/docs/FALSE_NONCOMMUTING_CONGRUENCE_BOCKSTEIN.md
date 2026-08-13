# Noncommuting congruence blocks survive both Bockstein kernels

Date: 2026-08-11

## 1. Outcome

The commuting lower-right congruence classes in
`FALSE_CONGRUENCE_TORSION_TORUS_CANCELLATION.md` disappear from the paired
ordinary/cyclotomic Bockstein quotient.  The noncommuting first-congruence
directions behave differently.  At the prime two they already give an
infinite-dimensional simultaneous obstruction.

Put

`R=Z[x_1^(+-1),...,x_d^(+-1)]`,
`E=EL_r(R)`, `r>=4`,
`E_2=ker(E->EL_r(R/2R))`,
`h=e_12(x_1^(-1))`,
`B_2=<E_2,h>`.                                           `(NCB1)`

Let `Z_-` be the rank-one integral `B_2`-module on which `E_2` acts
trivially and `h` acts by `-1`.  Write

`beta_+:H_2(B_2,F_2)->H_1(B_2,Z)`,
`beta_-:H_2(B_2,F_2)->H_1(B_2,Z_-)`                     `(NCB2)`

for the coefficient Bocksteins.  Then

`dim_(F_2) H_2(B_2,F_2)/(ker(beta_+)+ker(beta_-))`
` =infinity`.                                           `(NCB3)`

The same assertion holds for the actual limiting intermediate group

`H_2^fold=R_0 semidirect B_2`,                           `(NCB4)`

because `B_2->H_2^fold->B_2` is a split inclusion/retraction.  Thus the
local parity obstruction from `FALSE_PRIME_TWO_BOCKSTEIN_IDENTIFICATION.md`
does **not** vanish automatically.  The remaining marked problem is to
show that one of the classes below is selected by the radical filling
sequence, or to build a marked boundary which selects it.

## 2. The one-block calculation in `D_8`

Use the presentation

`D=<a,b,t | a^2=b^2=t^2=1, [a,b]=[a,t]=1,`
`                         t b t^(-1)=a b>`.             `(NCB5)`

This is the dihedral group of order eight.  Let `Z_-` also denote its sign
module, with `a,b` acting trivially and `t` acting by `-1`.  In the
normalized bar complex over `F_2`, define

`z_1=[t|t]`,
`z_2=[t|b]+[a b t|b]`,
`z_3=[b|t]+[a b t|b]+[a b t|a]+[a b t|a b t]`.          `(NCB6)`

Direct substitution in

`partial[g|k]=[k]-[gk]+[g] mod 2`                      `(NCB7)`

shows that all three chains are cycles.

**Lemma 1 (the dihedral paired quotient).**  The classes in `(NCB6)` are
a basis of `H_2(D,F_2)`, and

`ker(beta_+)=F_2(z_1+z_3)`,
`ker(beta_-)=F_2 z_1 directSum F_2 z_3`.                `(NCB8)`

Consequently

`H_2(D,F_2)/(ker(beta_+)+ker(beta_-))=F_2[z_2]`.        `(NCB9)`

**Proof.**  For a right rank-one local system with character `chi`, the
integral normalized bar boundary is

`partial_chi[g|k]=chi(g)[k]-[gk]+[g]`.                 `(NCB10)`

Applying `(NCB10)` to `(NCB6)` gives the following Bockstein table:

`                 beta_+                 beta_-`
`z_1              [t]                    0`
`z_2              [b]                   -[b]`
`z_3              [t]                    0`.           `(NCB11)`

For the last entry in the ordinary column, the half-boundary is

`[b]-[b t]+2[a b t]`,                                  `(NCB12)`

which equals `[t]` in

`H_1(D,Z)=C_2[b] directSum C_2[t]`.                     `(NCB13)`

For the sign system, the half-boundary of `z_3` is

`-[b t]-[a]+[a b t]`.                                  `(NCB14)`

The split extension

`1-><a,b>~=C_2^2->D-><t>~=C_2->1`                     `(NCB15)`

and its five-term sequence give

`H_1(D,Z_-)=C_2[b]`.                                   `(NCB16)`

Indeed `H_1(C_2,Z_-)=0`, the split transgression is zero, and

`H_1(C_2^2,Z)_(t,sign)`
` =C_2<a,b>/<(t-1)b=a>=C_2[b]`.                        `(NCB17)`

The cycle in `(NCB14)` maps to zero under `(NCB16)`, while `-[b]` does
not.  This proves the table.

It remains only to verify that the three displayed cycles exhaust degree
two.  The Lyndon--Hochschild--Serre spectral sequence for

`1->C_4=<b t>->D->C_2->1`                              `(NCB18)`

has three one-dimensional `E^2` terms in total degree two over `F_2`.
Hence `dim H_2(D,F_2)<=3`.

The first two cycles are independent because their ordinary Bocksteins are
the two independent generators in `(NCB13)`.  The remaining cycle
`z_1+z_3` is nonzero.  One completely explicit detector is the central
extension

`1-><R^4>~=C_2->D_16->D->1`,                           `(NCB19)`

where

`D_16=<R,T | R^8=T^2=1, T R T=R^(-1)>`,
`b t` lifts to `R`, and `t` lifts to `T`.               `(NCB20)`

For the section `(b t)^i t^j |-> R^i T^j`, `0<=i<4`, the associated
normalized `F_2`-valued two-cocycle is completely explicit.  If

`r=b t`, `g=r^i t^j`, `k=r^m t^n`, `0<=i,m<4`,

then it is the parity of the carry in

`i+(-1)^j m = (i+(-1)^j m mod 4)+4 c(g,k)`.             `(NCB20a)`

Substitution in `(NCB6)` gives

`<c,z_1>=0`, `<c,z_3>=1`,

so `<c,z_1+z_3>=1`.  Thus the three cycles are independent, the dimension
bound is sharp, and the table gives `(NCB8)--(NCB9)`.  End proof.

The key feature of `(NCB9)` is that `z_2` is not merely sent nontrivially
by both Bocksteins.  It lies outside the **sum** of the two kernels, which
is the stronger condition required by the integral pullback formula.

## 3. Infinitely many dihedral quotients of `B_2`

Let

`R_bar=F_2[x_1^(+-1),...,x_d^(+-1)]`.                  `(NCB21)`

The first congruence logarithm from `(CTC7)` is the equivariant
homomorphism

`theta_2:E_2->sl_r(R_bar)`,
`theta_2(1+2A)=A mod 2`.                                `(NCB22)`

For every Laurent monomial `f`, put

`A_f=f E_13`, `B_f=x_1 f E_23`.                        `(NCB23)`

Conjugation by `h_bar=1+x_1^(-1)E_12` satisfies

`Ad(h_bar)A_f=A_f`,
`Ad(h_bar)B_f=A_f+B_f`.                                 `(NCB24)`

The spaces

`U_f=F_2 A_f directSum F_2 B_f`                        `(NCB25)`

are independent invariant Jordan blocks.  The direct sum of these blocks
has an invariant complement in `sl_r(R_bar)`: in the column-three sector,
the monomial pairs in `(NCB23)` give the required decomposition, and no
other matrix-unit sector maps into that column under `Ad(h_bar)`.

Fix a finite set `S` of Laurent monomials and let

`phi_S:sl_r(R_bar)->V_S=directSum_(f in S) U_f`          `(NCB26)`

be the equivariant projection.  Since

`theta_2(h^2)=x_1^(-1)E_12`,                            `(NCB27)`

the extension class is killed by `phi_S`.  Every element of `B_2` has a
normal form `e h^epsilon`, with `e in E_2` and `epsilon in {0,1}`.  The
formula

`q_S(e h^epsilon)=(phi_S theta_2(e),epsilon)`           `(NCB28)`

therefore defines a surjective homomorphism

`q_S:B_2->Q_S=V_S semidirect C_2`.                     `(NCB29)`

For each `f in S`, the projection of `Q_S` onto

`U_f semidirect C_2`                                   `(NCB30)`

is the group `D` in `(NCB5)`, under

`a |-> A_f`, `b |-> B_f`, `t |-> h_bar`.               `(NCB31)`

## 4. The dihedral classes lift through the congruence kernel

Put `K_S=ker(q_S)`.  Choose the following lifts of the generators in
`(NCB31)`:

`a_f=e_13(2f)`,
`b_f=e_23(2x_1 f)`,
`t=h`.                                                  `(NCB32)`

The Steinberg relations give exact identities in `B_2`:

`[a_f,b_f]=[h,a_f]=1`,
`h b_f h^(-1)=a_f b_f`.                                `(NCB33)`

The two square defects are commutators entirely inside `K_S`.  Using the
auxiliary index four,

`a_f^2=e_13(4f)=[e_14(2f),e_43(2)]`,
`b_f^2=e_23(4x_1f)=[e_24(2x_1f),e_43(2)]`.             `(NCB34)`

All four commutator factors belong to `K_S`, because their first
congruence directions are killed by `(NCB26)`.

**Lemma 2 (zero transgression).**  For every `f in S`, the class `z_2` in
the `f`-th dihedral factor belongs to the image of

`H_2(B_2,F_2)->H_2(Q_S,F_2)`.                          `(NCB35)`

**Proof.**  The five-term sequence of

`1->K_S->B_2->Q_S->1`                                  `(NCB36)`

maps a bar cycle in `H_2(Q_S,F_2)` to its relator defect in
`H_1(K_S,F_2)_(Q_S)`.  Lift `z_2` using `(NCB32)`:

`Z_f=[h|b_f]+[a_f b_f h|b_f]`.                         `(NCB37)`

By `(NCB33)`, its mod-two boundary reduces to the difference between `h`
and `a_f^2 b_f^2 h`.  Hence its transgression is the class of

`a_f^2 b_f^2 in H_1(K_S,F_2)_(Q_S)`.                  `(NCB38)`

Both factors in `(NCB38)` belong to `[K_S,K_S]` by `(NCB34)`, so the
class is zero.  Exactness gives `(NCB35)`.  End proof.

## 5. The infinite paired quotient

For each `f in S`, choose

`alpha_f in H_2(B_2,F_2)`                              `(NCB39)`

mapping to the `f`-th class `z_2` under `(NCB35)`.  The classes `alpha_f`
are independent modulo `ker(beta_+)+ker(beta_-)`.

Indeed, suppose a linear combination of them belongs to that sum.  Map it
to `Q_S`, then project to the `f`-th dihedral factor.  Every class
`alpha_g`, `g!=f`, maps to zero there, while `alpha_f` maps to `z_2`.
Naturality sends each Bockstein kernel into the corresponding dihedral
kernel.  Lemma 1 therefore forces the coefficient of `alpha_f` to be zero.
This holds for every `f in S`.

Since `S` is an arbitrary finite set, this proves `(NCB3)`.

Finally, inclusion and projection give

`B_2 -> R_0 semidirect B_2 -> B_2`                     `(NCB40)`

with composite the identity.  If the image of a nonzero combination of
the `alpha_f` belonged to the sum of the two kernels in the larger group,
projection in `(NCB40)` would give the forbidden decomposition in `B_2`.
This proves `(NCB4)`.

## 6. What this proves and what remains

The calculation identifies the first explicit family which survives all
of the following losses simultaneously:

1. ordinary integral lifting;
2. sign-integral lifting;
3. commuting-root torus cancellation;
4. passage from the base congruence group to the free-fold intermediate
   group.

It is therefore a genuine local charge for the parity-gluing branch, not
merely torsion in one target group.  It does not yet prove FALSE.  The
marked radical filling class must still be shown to acquire a nonzero
coordinate along one `alpha_f` in finite covers, with the corresponding
integral repair norm escaping.

The bounded fixed-coset search in
`experiments/wild_fixed_coset_search.py` found no first-order common-lift
obstruction among `228` matched Laurent words.  That is consistent with
the theorem: the surviving classes come from nontrivial adjoint Jordan
blocks, rather than from the already-counted common-lift fixed-orbit
sector.  The next useful computation is the chain-level pairing between
the radical boundary and the quotient classes `(NCB39)`.
