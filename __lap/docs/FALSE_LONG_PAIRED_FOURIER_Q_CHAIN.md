# A long paired Fourier--Q chain with an undiluted inverse fold

Date: 2026-08-11

## 1. Outcome

The depth-one paired cell in
`FALSE_RADICAL_BS_PAIRED_FOURIER_Q_CELL.md` can be made arbitrarily long.
This is necessary because the common positive subgroup contains every fixed
forward compressor iterate, not only the first one.

Fix an odd prime `p`, put `q=1+p`, and let

`A_n=Z/p^n Z`, `V_n=A_n^3`, `Q_n=SL_3(A_n)`,          `(LPQ1)`

`c_0=diag(q,1,q^(-1))`, `a=e_1`.                     `(LPQ2)`

For every `M>=2`, there is a finite Hilbert space `H_(n,M)`, a common
`Q_n`-covariant additive representation `B_1(v)`, and two compressor
unitaries `S_(0,n,M),S_(1,n,M)` with the following properties.

For every `v in V_n` and every `0<=j<M`,

`Ad(S_(0,n,M)^j)(B_1(v))`
` =Ad(S_(1,n,M)^j)(B_1(v))`.                          `(LPQ3)`

Thus the two sectors agree exactly on the first `M` forward levels of the
positive additive orbit.  In the inverse direction,

`S_(0,n,M)^(-1)B_1(a)S_(0,n,M)=B_0(a)`,
`S_(1,n,M)^(-1)B_1(a)S_(1,n,M)=B_0(a)^q`.             `(LPQ4)`

For `n>=2`, the fold satisfies

`tr(B_0(a)^p)=0`,
`||B_0(a)^p-1||_2^2=2`.                               `(LPQ5)`

All identities are exact.  Taking any sequence `M_n->infinity` therefore
gives agreement on every fixed forward positive depth while the inverse
fold remains undiluted.  No boundary fraction appears in `(LPQ5)`.

The construction is functorial in the additive module.  In particular the
same cyclic-polarization device applies to a finite Frobenius model of the
full square-zero tangent module once its base action and monomial depth maps
have been supplied.  The remaining global problem is to construct that
module so all external generators, not only the chosen compressor, act
coherently with the elementary base group.

## 2. A cyclic Lagrangian basis

Put

`H_(n,M)=ell^2(Q_n times V_n^M)`.                     `(LPQ6)`

Write a point of `V_n^M` as `(x_0,...,x_(M-1))` and use the perfect pairing

`<x,v>=x^T v/p^n mod Z`.                              `(LPQ7)`

For `v in V_n`, define

`B_0(v)delta_(g,x_0,...,x_(M-1))`
` =e(<x_0,g^(-1)v>)delta_(g,x_0,...,x_(M-1))`,        `(LPQ8)`

and, for `1<=j<M`,

`B_j(v)delta_(g,x_0,...,x_j,...,x_(M-1))`
` =delta_(g,x_0,...,x_j+g^(-1)v,...,x_(M-1))`.        `(LPQ9)`

Every `B_j` is an additive representation of `V_n`.  The families for
different `j` commute.  Let

`L_n(u)delta_(g,x)=delta_(ug,x)`.                     `(LPQ10)`

As in `(PFQ15)`, all families are exactly covariant:

`L_n(u)B_j(v)L_n(u)^(-1)=B_j(uv)`.                   `(LPQ11)`

Let `X_j(v)` denote translation by `g^(-1)v` in the `j`th coordinate,
including `j=0`.  Choose a Fourier transform `F_0` on the zeroth coordinate
so that

`F_0 X_0(v)F_0^(-1)=B_0(v)`.                         `(LPQ12)`

Then

`B_j(v)=F_0 X_j(v)F_0^(-1)`                           `(LPQ13)`

for every `j`: for `j>=1`, `F_0` acts on another coordinate and does
nothing.

Let `P_M` cyclically permute the `M` coordinates so that

`P_M X_j(v)P_M^(-1)=X_(j+1 mod M)(v)`.               `(LPQ14)`

Set

`S_(0,n,M)=F_0 P_M F_0^(-1)`.                        `(LPQ15)`

Equations `(LPQ13)--(LPQ15)` give the exact cyclic law

`S_(0,n,M)B_j(v)S_(0,n,M)^(-1)`
` =B_(j+1 mod M)(v)`.                                 `(LPQ16)`

The operator in `(LPQ15)` commutes with the left `Q_n` action because all
fiber operations are independent of `g`.  It also has order exactly
dividing `M`, being conjugate to `P_M`.

## 3. The gauge fixes the positive arc and shears its predecessor

Put

`K_n=q^(-1)c_0^T`.                                    `(LPQ17)`

Define the permutation unitary `T_(n,M)` by

`T_(n,M)delta_(g,x_0,x_1,...,x_(M-1))`
` =delta_(g c_0,K_nx_0,c_0^(-1)x_1,...,`
`                         c_0^(-1)x_(M-1))`.          `(LPQ18)`

The calculation `(PFQ21)--(PFQ22)` applies coordinatewise and gives

`[T_(n,M),B_j(v)]=1` for `1<=j<M`,                    `(LPQ19)`

`T_(n,M)B_0(v)T_(n,M)^(-1)=B_0(v)^q`.                `(LPQ20)`

Moreover `T_(n,M)` commutes with the left `Q_n` action.  Define the second
compressor by

`S_(1,n,M)=S_(0,n,M)T_(n,M)^(-1)`.                   `(LPQ21)`

Starting at `B_1(v)`, the first `M-1` forward steps encounter only
`B_1(v),...,B_(M-1)(v)`, on all of which `(LPQ19)` applies.  Induction using
`(LPQ16)` proves `(LPQ3)` for `0<=j<M`.  At the next step the orbit reaches
`B_0`, and the two actions can differ; this is precisely why the finite
chain is not sterile.

In the inverse direction, `(LPQ16)` gives

`S_(0,n,M)^(-1)B_1(a)S_(0,n,M)=B_0(a)`.              `(LPQ22)`

Using `(LPQ20)--(LPQ21)`,

`S_(1,n,M)^(-1)B_1(a)S_(1,n,M)`
` =T_(n,M)B_0(a)T_(n,M)^(-1)=B_0(a)^q`.              `(LPQ23)`

This proves `(LPQ4)`.

## 4. Exact marked trace and the stable coefficient action

For fixed `g`, averaging `(LPQ8)` over `x_0` gives

`(1/|V_n|)sum_(x_0 in V_n)e(<x_0,p g^(-1)a>)=0`      `(LPQ24)`

because `p g^(-1)a` is nonzero when `n>=2`.  The other coordinates merely
multiply the zero sum.  This proves `(LPQ5)`.

Let

`C_(n,M)=L_n(c_0)`.                                   `(LPQ25)`

It commutes with `F_0`, `P_M`, and `T_(n,M)`, and

`C_(n,M)B_j(a)C_(n,M)^(-1)=B_j(a)^q`                 `(LPQ26)`

for every `j`.  Thus the coefficient component of the marked
Baumslag--Solitar stable letter is exact on the whole cyclic chain.

The matrices `S_(i,n,M)` normalize the finite Pauli group on `V_n^M` and
have finite order by the projective-normalizer argument in
`FALSE_PAIRED_FOURIER_PRINCIPAL_BUNDLE_SPLICE.md`.  Consequently the exact
principal-bundle theorem applies to both compressor choices.  After one
common congruence enlargement, they extend to exact representations of the
entire external `SL_d(Z)`, with the commuting transvection `s` carrying
trivial fiber holonomy.

## 5. What is now reduced

For the marked one-compressor orbit, there is no longer a conflict between
long positive agreement and positive fold energy.  The exact finite data
are:

* common coefficient `Q_n` covariance;
* agreement on `M` successive positive tangent levels;
* exact external `SL_d(Z)` representations with the compressor prescribed;
* exact marked `t,s,c_0` relations; and
* fold energy equal to two.

The remaining completion is not a longer clock calculation.  It is the
simultaneous coefficient functor:

> construct a finite Frobenius representation of the polynomial elementary
> group whose tangent images along every tested compressor orbit are the
> Lagrangian families `(LPQ8)--(LPQ9)`, and whose base elementary action
> preserves their pairings and Steinberg commutator products.

Once that is done for increasing finite windows, `(LPQ3)` supplies the
amalgam agreement and `(LPQ5)` triggers the marked endpoint `(PFQ32)--(PFQ36)`.
