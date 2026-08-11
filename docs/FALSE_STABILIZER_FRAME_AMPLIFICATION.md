# Stabilizer-frame amplification cancels the transfer loss

Date: 2026-08-11

## 1. Outcome

Let `X=D/K` be a finite regular presentation cover, let `w` be a radical
word, and let a finite deck subgroup `A` of order `m` stabilize the ordinary
homology class of the lifted `w`-loop.  Put `H/K=A`.  If `q` is the minimum
real filling of the loop in `X` and `P_A` is deck averaging, then the exact
marked ratio satisfies

`Lambda_(w,X)>=sqrt(m)||P_Aq||`
`             =Fill_R,2(w;H)`.                         `(SFA1)`

The first equality is the orbit-frame effect: the `m` word coordinates in
the `A`-orbit all evaluate to the same scalar on the invariant vector
`P_Aq`.  The second is exact quotient scaling.

Thus the `m^(-1/2)` loss in the norm of invariant transfer is not a loss in
the **marked** problem.  The marked analysis operator repeats the invariant
coefficient `m` times and restores the missing factor `sqrt(m)`.

For the explicit Laurent-double tower, this improves the remaining real
branch to

`Fill_R,2(w;H_n)->infinity  =>  FALSE`,                `(SFA2)`

with no comparison to `sqrt(m_n)`.  The only surviving branch is bounded
intermediate real filling together with divergent integral discriminant
radius.

## 2. Infinitesimal form of the marked ratio

Use the notation of
`FALSE_MARKED_DISCRIMINANT_DIVERGENCE_CRITERION.md`.  On a finite exact
chart `X`, let

`W_X=ran(d_X^1)`                                       `(SFA3)`

and let

`T_X:W_X->R^X`,
`(T_Xy)_z=<q_(w,z),y>`                                 `(SFA4)`

be the marked analysis operator.  The exact nonlinear ratio is

`Lambda_(w,X)`
` =sup_(y in W_X-L_X)`
`   dist(T_Xy,Z^X)/dist(y,Z^(X times R)).`             `(SFA5)`

**Lemma 1 (tangent operator bound).**  For every nonzero `y in W_X`,

`Lambda_(w,X)>=||T_Xy||/||y||`.                        `(SFA6)`

Consequently `Lambda_(w,X)>=||T_X||_op`.

**Proof.**  For all sufficiently small positive `t`, avoiding at most a
discrete set for which `ty in L_X`, zero is the closest ambient integral
vector to `ty` and zero is the closest integral vector to `tT_Xy`.  Hence

`dist(T_X(ty),Z^X)/dist(ty,Z^(X times R))`
` =||T_Xy||/||y||`.                                   `(SFA7)`

Take the supremum and then the supremum over `y`.  End proof.

This is the full orbit-frame strengthening of the one-vector estimate
`Lambda>=||q_(w,x)||` from
`FALSE_REAL_FILLING_ESCAPE_DICHOTOMY.md`.

## 3. Repetition on an invariant orbit

Assume now that `X=D/K` is regular.  Let `A<=D/K` be a finite deck subgroup
of order `m`, and let

`P=(1/m)sum_(a in A)a`                                  `(SFA8)`

be its orthogonal averaging projection on cellular chains and cochains.
Fix the loop at the identity vertex and write

`b=b_(w,1)`, `q=q_(w,1)`.                              `(SFA9)`

Equivariance and uniqueness of the minimum real filling give

`q_(w,a)=a q`                                          `(SFA10)`

for every deck element `a`.

Put

`r=Pq`.                                                `(SFA11)`

Then `r` is `A`-invariant and, because `P` is an orthogonal projection,

`<q,r>=||r||^2`.                                       `(SFA12)`

**Theorem 2 (stabilizer-frame lower bound).**

`Lambda_(w,X)>=sqrt(m)||r||`.                          `(SFA13)`

**Proof.**  For each `a in A`, equations `(SFA4)`, `(SFA10)--(SFA12)` give

`(T_Xr)_a=<a q,r>=<q,a^(-1)r>=<q,r>=||r||^2`.         `(SFA14)`

Thus at least `m` coordinates of `T_Xr` have the displayed value, and

`||T_Xr||>=sqrt(m)||r||^2`.                            `(SFA15)`

If `r!=0`, apply Lemma 1 with `y=r`.  If `r=0`, `(SFA13)` is immediate.
End proof.

No modular reduction occurs in this argument: it is the tangent of the
exact torus ratio at the origin.  Hence even an integral value of
`||r||^2` causes no cancellation.

## 4. Exact cancellation of quotient scaling

Suppose `A=H/K`, so `Y_K->Y_H` is a regular cover of degree `m`.  Let

`J^!:C_*(Y_H,R)->C_*(Y_K,R)`                          `(SFA16)`

be constant lift.  The orbit-average formula from
`FALSE_NONAMENABLE_STABILIZER_FILLING_REDUCTION.md` gives

`Pb=(1/m)J^!b_H`.                                     `(SFA17)`

Since `r=Pq` and `d^1` commutes with deck averaging, `r` is the unique
minimum real filling of `Pb`.  Exact quotient scaling therefore gives

`||r||=m^(-1/2)Fill_R,2(w;H)`.                        `(SFA18)`

Combining `(SFA13)` and `(SFA18)` proves the promised identity:

**Corollary 3 (transfer loss cancellation).**

`Lambda_(w,X)>=Fill_R,2(w;H)`.                         `(SFA19)`

This conclusion does not require property `(T)`.  Property `(T)` is useful
for comparing the full filling `q` to its invariant part `r`; the marked
lower bound only uses invariance and exact quotient scaling.

## 5. Application to the Laurent radical double

Use

`pi:D=G *_Gamma G->F=G *_E G`,                        `(SFA20)`

the constant Kazhdan subgroup `J=SL_3(Z)<=F`, a normal finite-index
subgroup `L_n normal F`, and

`K_n=pi^(-1)(L_n)`, `H_n=pi^(-1)(J L_n)`.             `(SFA21)`

The deck group of `Y_(K_n)->Y_(H_n)` is

`A_n=J/(J intersect L_n)`.                             `(SFA22)`

The homology class of the marked loop is fixed by `J`, so the setup of
Corollary 3 applies.  Therefore

`Lambda_(w,D/K_n)>=Fill_R,2(w;H_n)`                    `(SFA23)`

at every level.

**Corollary 4 (intermediate real escape proves FALSE).**  If the right
side of `(SFA23)` is unbounded along any relatively separating tower, then
a hyperlinear nonsofic group exists.

**Proof.**  The marked ratios on the finite exact charts `D/K_n` are
unbounded by `(SFA23)`.  Apply the marked discriminant divergence theorem.
End proof.

For the relatively separating tower of
`FALSE_CONSTANT_STABILIZER_SEPARABILITY.md`, integral filling escape says

`Fill_Z,2(w;H_n)->infinity`.                           `(SFA24)`

The exact Pythagoras identity downstairs now leaves only the dichotomy

1. `Fill_R,2(w;H_n)` is unbounded, and Corollary 4 proves FALSE;
2. along a bounded-real subsequence,
   `rho_(H_n)(c_(H_n))->infinity`.

Unlike the earlier formulation, there is no super-square-root growth gate.
The transfer degree may grow arbitrarily; the orbit frame cancels it
exactly.

## 6. The exact residual arithmetic gate

In the bounded-real branch, let `q_n` be the canonical real filling and
`c_n` its canonical discriminant class in the intermediate cover.  The
paired carry identity gives the useful pointwise bound

`delta(c_n)<=rho_L(gamma(c_n))<=||q_n||`.              `(SFA25)`

Thus the escaping class itself has uniformly bounded **exact carry energy**
even though its cycle-side radius tends to infinity.  What is not automatic
is marked visibility: its word vector is the discriminant Gram row

`(<q_(w,z),q_n> mod Z)_(z in D/H_n)`.                 `(SFA26)`

A nonuniform family of translates with bounded carry incidence and growing
word incidence would finish FALSE by
`FALSE_BERNOULLI_CARRY_INCIDENCE.md`.  Total isotropy can make `(SFA26)`
vanish, so divergent radius alone still does not prove that incidence
separation.

The remaining gap is therefore narrower than before:

> In the bounded-real, divergent-discriminant branch, prove that the
> canonical low-carry classes have an unbounded marked Gram/incidence
> profile, or prove that total isotropy would force a bounded integral
> filling.

This is the sole place where the integral lattice geometry, rather than
real transfer, remains load-bearing.
