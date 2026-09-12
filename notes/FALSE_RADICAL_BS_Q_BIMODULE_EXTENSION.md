# The Baumslag--Solitar clock extends exactly over the coefficient Q-action

Date: 2026-08-11

## 1. Outcome

The frozen clock does not have to be extended over the coefficient group

`Q=SL_3(Z[1/q])`, `q=1+p`,                            `(QBE1)`

by a nonlinear matrix search.  There is an exact finite bimodule model.

For `k>=2`, put `n=k+1`,

`A_n=Z/p^n Z`, `V_n=A_n^3`, `Q_n=SL_3(A_n)`,          `(QBE2)`

and let

`c_0=diag(q,1,q^(-1)) in Q_n`, `a=e_1 in V_n`.        `(QBE3)`

On `H_n=ell^2(Q_n)` there are:

1. an exact representation `D_n` of the additive square-zero coefficient
   module `V_n`;
2. the left regular representation `L_n` of `Q_n`, satisfying all
   semidirect covariance relations exactly; and
3. a right translation `T_n` which commutes with the whole left `Q_n`
   action and satisfies

`T_n^(-1) D_n(a) T_n=D_n(a)^q`.                       `(QBE4)`

Consequently the two exact local fold sectors

`h_(1,n)=D_n(a)`, `h_(2,n)=D_n(a)^q`                  `(QBE5)`

have

`tr_(H_n)(h_(2,n)h_(1,n)^(-1))=0`,
`||h_(2,n)h_(1,n)^(-1)-1||_2^2=2`.                   `(QBE6)`

Thus the clock mechanism extends through the entire finite `Q_n` orbit
without losing the macroscopic fold witness.  The right operator in
`(QBE4)` already commutes with every coefficient-`Q` generator, as the
external substitution generator must.

The extension has been reduced to the external substitution group and the
remaining elementary tangent module.  In the present model, the external
generators must be represented inside the explicit finite algebra

`L_n(Q_n)'`,                                           `(QBE7)`

with the chosen compressor fixed to `T_n`.  The abstract external-group
part is solved by the prescribed-generator theorem in
`FALSE_PRESCRIBED_GENERATOR_COMMUTANT_COMPLETION.md`: after multiplicity
amplification, all fixed `SL_d(Z)` relators have defect tending to zero.
The remaining variables are only those enforcing its Laurent-monomial and
base-elementary covariance.

## 2. The finite coefficient representation

Let

`ell(v)=v_1/p^n mod Z`, `v in V_n`,                   `(QBE8)`

and write `e(x)=exp(2 pi i x)`.  For `v in V_n`, define the diagonal
unitary

`D_n(v) delta_g=e(ell(g^(-1)v)) delta_g`,              `(QBE9)`

where `g in Q_n`.  Additivity of `ell` gives

`D_n(v+w)=D_n(v)D_n(w)`.                              `(QBE10)`

For `u,b in Q_n`, use the commuting left and right translations

`L_n(u)delta_g=delta_(ug)`,
`R_n(b)delta_g=delta_(gb)`.                            `(QBE11)`

Direct substitution gives

`L_n(u)D_n(v)L_n(u)^(-1)=D_n(uv)`.                    `(QBE12)`

Indeed, on `delta_g` the phase on the left is

`e(ell(g^(-1)uv))`.

Equations `(QBE10)--(QBE12)` are exactly the additive and `Q_n`-covariance
relations of the coefficient square-zero module.  No approximation has
been used.

## 3. The commuting right compressor

The first coordinate functional satisfies

`ell(c_0 x)=q ell(x) mod Z`.                           `(QBE13)`

Using `(QBE9)--(QBE11)`, one obtains

`R_n(c_0)D_n(v)R_n(c_0)^(-1)=D_n(v)^q`.               `(QBE14)`

The convention in the Kun--Thom pair is

`h=t^(-1) gamma t`.                                   `(QBE15)`

Set

`T_n=R_n(c_0)^(-1)`, `Gamma_n=D_n(a)`.                `(QBE16)`

Then `(QBE14)` says

`T_n^(-1) Gamma_n T_n=Gamma_n^q`.                     `(QBE17)`

Moreover

`[T_n,L_n(u)]=1` for every `u in Q_n`.                `(QBE18)`

Thus `(QBE17)` realizes the two fold sectors in `(QBE5)`, while `(QBE18)`
is exactly the direct-product commutation required between the external
substitution generator and the common coefficient group.

The stable-letter relation is exact as well.  Put

`C_n=L_n(c_0)`.                                        `(QBE19)`

Then `(QBE12)` gives

`C_n Gamma_n C_n^(-1)=Gamma_n^q`,                     `(QBE20)`

and left/right commutation gives `[C_n,T_n]=1`.  Hence both pairs
`(Gamma_n,C_n)` and `(Gamma_n^q,C_n)` are exact representations of the
marked `BS(1,q)` slice, including the required commutation of the two
external directions used in the fold-aligned construction.

## 4. Exact trace of the fold

The group `Q_n` acts transitively on the primitive vectors of `V_n`.
Indeed a primitive column over the local principal ideal ring `A_n`
extends to an invertible basis, and the determinant can be corrected to
one in a complementary column.  Therefore, as `g` runs uniformly over
`Q_n`, the vector `g^(-1)a` is uniform on

`Prim(V_n)=V_n minus pV_n`.                            `(QBE21)`

The fold in `(QBE5)` is

`Gamma_n^(q-1)=Gamma_n^p`.                            `(QBE22)`

Its normalized trace is the primitive-vector average

`(1/|Prim(V_n)|) sum_(x in Prim(V_n))`
`  exp(2 pi i x_1/p^k)`.                              `(QBE23)`

For `k>=2`, both the sum over all `x in V_n` and the sum over all
`x in pV_n` vanish.  The first contains the factor

`sum_(r mod p^n) exp(2 pi i r/p^k)=0`;                `(QBE24)`

after writing `x=py`, the second contains

`sum_(s mod p^k) exp(2 pi i s/p^(k-1))=0`.            `(QBE25)`

Subtracting the divisible vectors from all vectors proves the first line
of `(QBE6)`.  For any unitary `U`,

`||U-1||_2^2=2-2 Re tr(U)`,                           `(QBE26)`

so the second line follows.

This calculation is the full-`Q_n` version of the orbit computation in
`FALSE_RADICAL_BS_CLOCK_AVERAGE_NO_GO.md`.  Right multiplication by `c_0`
partitions `Q_n` into cycles of length `p^k`, and on each cycle the phases
in `(QBE9)` form a rotated clock orbit.  Completing all `Q_n` translates
does not dilute the aggregate marked displacement.

## 5. The remaining constrained external problem

Let `L=SL_d(Z)` be the external substitution factor and let `t` denote the
compressor `I+e_12`.  Because `Q` and `L` commute in the ambient group, any
extension of the block above must assign the external generators to
unitaries in

`A_n=L_n(Q_n)'`.                                       `(QBE27)`

The distinguished assignment is fixed:

`U_t=T_n=R_n(c_0)^(-1)`.                              `(QBE28)`

Choose a finite presentation `L=<S_L|R_L>` containing `t` in its generating
window.  The first computational obstruction is the explicit number

`epsilon_n^(L)=inf max_(r in R_L)||r((U_s)_(s in S_L))-1||_2`,
                                                                  `(QBE29)`

where the infimum is over `U_s in U(A_n)` and `(QBE28)` is imposed.

Theorem 1 of
`FALSE_PRESCRIBED_GENERATOR_COMMUTANT_COMPLETION.md` proves, after replacing
`A_n` by `A_n tensor M_(r_n)` for suitable multiplicities,

`epsilon_n^(L)->0`.                                   `(QBE29a)`

Thus the resulting unitaries solve all abstract `Q times L` relations and
leave only their covariance on the Laurent tangent module and the base
elementary group.

The search algebra has an exact block decomposition.  Peter--Weyl gives

`ell^2(Q_n)=directSum_(pi in Irr(Q_n)) V_pi tensor C^(dim pi)`,

`A_n=directSum_pi 1_(V_pi) tensor M_(dim pi)(C)`.       `(QBE30)`

Under `(QBE30)`, the fixed matrix `T_n` is the corresponding direct sum of
the contragredient matrices `pi(c_0)^(-1)` on the multiplicity factors.
Thus `(QBE29)` is a weighted family of finite matrix-relation problems,
not an optimization in dimension `|Q_n|` with no symmetry.

There is one further compulsory layer after `(QBE29a)`: the external
unitaries must implement the prescribed monomial substitutions on the
full square-zero tangent module

`sl_r(V_n[x_1^(+-1),...,x_d^(+-1)])`.                 `(QBE31)`

Equations `(QBE10)--(QBE20)` already solve its coefficient-`V_n` and
coefficient-`Q_n` slice.  The unsolved variables are precisely the
monomial labels, the base elementary conjugations, and the external
generators other than the frozen compressor.  This is the correct reduced
version of the proposed “freeze the clock and solve only for the added
variables” experiment.

## 6. Scope

The construction is an exact finite-dimensional representation of the
subgroup generated by the additive coefficient module, `Q_n`, the marked
coefficient element, and the two commuting operators `(QBE16),(QBE19)`.
It is not a representation of `G` or of its double, because the tangent
covariance `(QBE31)` has not been solved.  The abstract external relation
problem `(QBE29)` is solved after amplification by `(QBE29a)`.

It nevertheless removes a substantial family of variables from the final
extension problem.  In particular, failure of a naive single clock orbit
to be `Q`-invariant is not an obstruction: its exact `Q_n`-orbit completion
retains the fold with squared normalized displacement `2`.
