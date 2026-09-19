# The noncommuting Bockstein blocks are killed by polynomial stabilizers

Date: 2026-08-11

## 1. Outcome

The infinite paired-Bockstein quotient constructed in
`FALSE_NONCOMMUTING_CONGRUENCE_BOCKSTEIN.md` is genuine in the base
congruence group, but its displayed generators do not couple to the
Bass--Serre relation module of the Laurent radical word.

Keep

`R=Z[x_1^(+-1),...,x_d^(+-1)]`,
`R_+=Z[x_1,...,x_d]`,
`E=EL_r(R)`, `Gamma=EL_r(R_+)`, `r>=5`,
`E_2=ker(E->EL_r(R/2R))`,
`h=e_12(x_1^(-1))`, `B_2=<E_2,h>`.                    `(NSC1)`

For a Laurent monomial `f`, put

`a_f=e_13(2f)`, `b_f=e_23(2x_1f)`, `t=h`.             `(NSC2)`

The quotient used in the preceding note sends these elements to the
standard generators `a,b,t` of `D_8`, and the surviving paired class maps
to

`z_2=[t|b]+[a b t|b] in H_2(D_8,F_2)`.                `(NSC3)`

The new observation is:

1. `z_2=[b|b]` in `H_2(D_8,F_2)`;
2. for every `f`, the square class `[b|b]` has a cycle lift inside a
   conjugate of the polynomial stabilizer `Gamma`; and consequently
3. its connecting class in the augmentation module of `E/Gamma` is zero.

Thus all the explicit classes from the noncommuting Jordan blocks belong
to the stabilizer-homology image in the permutation-module exact sequence.
They cannot by themselves be the marked finite-support charge required by
the radical filling sequence.

This does not prove that the entire simultaneous Bockstein quotient of the
Laurent intermediate group is unmarked.  It closes the particular infinite
family `(NCB39)`: a surviving class must also survive quotienting by the
homology of **all** polynomial double-coset stabilizers.

## 2. The dihedral generator is a square class

Use the presentation

`D=<a,b,t | a^2=b^2=t^2=1, [a,b]=[a,t]=1,`
`                         t b t^(-1)=a b>`.           `(NSC4)`

Recall the three-cycle basis from `(NCB6)`:

`z_1=[t|t]`,
`z_2=[t|b]+[a b t|b]`,
`z_3=[b|t]+[a b t|b]+[a b t|a]+[a b t|a b t]`.        `(NSC5)`

Let

`u_b=[b|b]`.                                          `(NSC6)`

It is a mod-two bar cycle because `b^2=1`.  Its ordinary and sign
Bocksteins are both `[b]`.  The sign system is trivial on `<b>`, and the
minus sign in `(NCB11)` is immaterial on the order-two target.  Hence

`beta_+(u_b)=beta_+(z_2)=[b]`,
`beta_-(u_b)=beta_-(z_2)=[b]`.                        `(NSC7)`

By `(NCB8)`, the common kernel of the two Bocksteins is

`ker(beta_+) intersect ker(beta_-)=F_2(z_1+z_3)`.     `(NSC8)`

The `D_16` extension cocycle `(NCB20a)` evaluates to zero on `u_b`.
Indeed, with `r=bt`, one has `b=rt`, and the product `b b=1` creates no
carry modulo four.  More explicitly,

`c(b,b)=0`, `c(t,b)=1`, `c(abt,b)=1`.                `(NSC8a)`

Thus the same cocycle evaluates to zero on `z_2`, while it evaluates to
one on `z_1+z_3`.  Therefore `(NSC7)--(NSC8)` force

`u_b=z_2 in H_2(D,F_2)`.                             `(NSC9)`

This identity is the reason the noncommuting class can be absorbed by a
stabilizer even though it is outside the sum of the two Bockstein kernels.

## 3. A polynomial stabilizer containing the square filling

Write the monomial in `(NSC2)` as `f=x^u` and put

`v=u+e_1 in Z^d`, so `x_1f=x^v`.                     `(NSC10)`

Besides `b_f`, define

`p_f=e_24(2x^v)`, `c_f=e_43(2)`.                     `(NSC11)`

The Steinberg commutator relation gives the exact identity

`[p_f,c_f]=e_23(4x^v)=b_f^2`.                         `(NSC12)`

Choose the determinant-one Laurent diagonal matrix whose exponent weights
on coordinates `2,3,4,5` are

`lambda_2=0`, `lambda_3=lambda_4=-v`, `lambda_5=2v`, `(NSC13)`

and whose remaining weights are zero.  Denote it by `d_f`.  A diagonal
matrix of the form `diag(u,u^(-1),1,...)` is elementary in stable rank, so
`d_f in E`.

For a root element, conjugation satisfies

`d_f^(-1)e_ij(x^c)d_f=e_ij(x^(c+lambda_j-lambda_i))`.
                                                               `(NSC14)`

Equations `(NSC10)--(NSC14)` give

`d_f^(-1)b_f d_f=e_23(2)`,
`d_f^(-1)p_f d_f=e_24(2)`,
`d_f^(-1)c_f d_f=e_43(2)`.                         `(NSC15)`

All three elements therefore belong to the conjugate polynomial subgroup

`Gamma_f=d_f Gamma d_f^(-1)`.                         `(NSC16)`

They also belong to `B_2`.  Under the one-block quotient

`q_f:B_2->D`,                                         `(NSC17)`

one has

`q_f(b_f)=b`, `q_f(p_f)=q_f(c_f)=1`.                 `(NSC18)`

There is an explicit normalized bar cycle in
`B_2 intersect Gamma_f`.  Put

`P_f=[p_f|c_f]+[p_fc_f|p_f^(-1)]`
`    +[p_fc_fp_f^(-1)|c_f^(-1)]`
`    +[p_f|p_f^(-1)]+[c_f|c_f^(-1)]`,                `(NSC19)`

and

`U_f=[b_f|b_f]+P_f`.                                  `(NSC20)`

In the mod-two normalized bar complex, telescoping gives

`partial P_f=[[p_f,c_f]]=[b_f^2]`,
`partial[b_f|b_f]=[b_f^2]`.                           `(NSC21)`

Thus `U_f` is a cycle.  Equations `(NSC18)--(NSC19)` show that

`(q_f)_*[U_f]=[b|b]=z_2`.                             `(NSC22)`

Consequently the paired class used in `(NCB39)` may be chosen to be the
image of a class in

`H_2(B_2 intersect d_f Gamma d_f^(-1),F_2)`.          `(NSC23)`

Notice that this is stronger than merely conjugating `b_f` into the
polynomial subgroup: the entire commutator filling of its square is
conjugated there simultaneously.

## 4. Vanishing of the relation-module transgression

Let

`P=E/Gamma`, `I_P=Aug_(F_2)(P)`.                     `(NSC24)`

Restrict the transitive `E`-set `P` to `B_2`.  Its orbits are indexed by
double cosets `B_2\E/Gamma`, and the stabilizer of the point `d Gamma` is

`S_d=B_2 intersect d Gamma d^(-1)`.                   `(NSC25)`

Shapiro's lemma and the coefficient sequence

`0->I_P->F_2[P]->F_2->0`                              `(NSC26)`

give the exact segment

`directSum_(B_2 d Gamma) H_2(S_d,F_2)`
` ->H_2(B_2,F_2) --delta_P--> H_1(B_2,I_P)`.          `(NSC27)`

Take `d=d_f`.  Formula `(NSC23)` says that the displayed representative of
the `f`-th paired class lies in the image of the first arrow in `(NSC27)`.
Exactness therefore gives

`delta_P([U_f])=0`.                                   `(NSC28)`

The identity fiber of the fold relation module is precisely `I_P`:

`(R_0)_ab`
` ~=directSum_(ell in F/E) Aug_Z(E/(ell Gamma ell^(-1)))`.
                                                               `(NSC29)`

The marked word

`w=i_2(h)i_1(h)^(-1)`                                 `(NSC30)`

lies in this identity fiber and is represented by

`e_h=delta_(hGamma)-delta_Gamma`.                     `(NSC31)`

Thus `(NSC28)` is exactly the failure of the displayed dihedral class to
produce a derived augmentation-homology charge in the same relation-module
fiber as the radical word.

For a finite set of monomials, the cycles `U_f` still project to the
independent classes `z_2` in the corresponding dihedral factors.  Hence
they retain the independence modulo the two Bockstein kernels proved in
`(NCB39)`, while every one of them is killed by `(NSC27)`.  The two facts
are compatible: the paired Bockstein quotient of the base group is larger
than the quotient which remains after imposing all Bass--Serre stabilizer
relations.

## 5. Consequence for the FALSE search

The chain-level pairing requested at the end of
`FALSE_NONCOMMUTING_CONGRUENCE_BOCKSTEIN.md` is zero for the explicit
Jordan-block generators.  Their survival through the congruence kernel did
not test survival through the polynomial double-coset stabilizers.

The correct local object is therefore the further quotient

`H_2(B_2,F_2) /`
` (ker(beta_+)+ker(beta_-)`
`  +sum_d im(H_2(S_d,F_2)))`.                         `(NSC32)`

Only a nonzero class in `(NSC32)`, or a derived exterior-square class not
coming from the base row, can couple to the radical relation module.  The
displayed `D_8` blocks vanish in `(NSC32)` by `(NSC23)`.

This closes one tempting route but sharpens the next computation.  A
future finite search must quotient stabilizer **homology**, not only
stabilizer fixed points or first-order adjoint deformations.  Equivalently,
it must search for a paired class which no polynomially conjugated square
or higher stabilizer relation can fill.
