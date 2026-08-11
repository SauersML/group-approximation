# The TRUE domination gap is singular or dimension-uniform

Date: 2026-08-11

## Purpose

`TRUE_RADICAL_DOMINATION_CONSTANTS.md` reduces the assertion that every
hyperlinear group is sofic to one comparison.  For a finite presentation

`P=<s_1,...,s_k | R>`

and a word `w`, finiteness of the permutation domination constant must imply
finiteness of the finite-dimensional character domination constant.

This note separates the latter problem into two exact layers.  In each fixed
matrix dimension it is a real-algebraic Lipschitz error-bound problem.  The
bound holds automatically at every constant-rank exact projective solution.
Consequently a failure is forced either by a singular finite-dimensional
solution and a bad arc through it, or by degeneration as the dimension tends
to infinity.

No sofic approximation or selected `SL_3(Z)` chart is used here.

## 1. Fixed-dimensional defect maps

Fix `d>=1` and put

`X_d=U(d)^k`.                                                `(FDA1)`

A point `U=(U_1,...,U_k)` defines a representation
`pi_U:F_k->U(d)`.  Write

`chi_U(g)=tr_d(pi_U(g))`,
`q_U(g)=1-|chi_U(g)|^2`,
`Q_R(U)=sum_(r in R) q_U(r)`.                                `(FDA2)`

The conjugate-double representation

`hat pi_U=pi_U tensor conjugate(pi_U)`                        `(FDA3)`

has normalized character `|chi_U|^2`.  With normalized Hilbert--Schmidt
norms, define

`Phi_d(U)=(hat pi_U(r)-1)_(r in R)`,
`Psi_d(U)=hat pi_U(w)-1`.                                    `(FDA4)`

Then exactly

`||Phi_d(U)||_2^2=2 Q_R(U)`,
`||Psi_d(U)||_2^2=2 q_U(w)`.                                 `(FDA5)`

Both maps are real polynomial in the real and imaginary matrix entries,
restricted to the compact real-algebraic manifold `X_d`.

Assume from now on that the permutation domination constant is finite:

`C_perm(P,R,w)<infinity`.                                    `(FDA6)`

By the radical characterization in
`TRUE_RADICAL_DOMINATION_CONSTANTS.md`, `(FDA6)` says

`w in Rad_sof(P)`.                                           `(FDA7)`

It also gives the exact zero-set containment

`Phi_d(U)=0  ==>  Psi_d(U)=0`.                               `(FDA8)`

Indeed, `Phi_d(U)=0` says that every `pi_U(r)` is scalar, so `hat pi_U`
factors through `P`.  Its image is a finitely generated linear group and is
therefore residually finite and sofic.  Equation `(FDA7)` forces that image
to kill `w`.

Define the dimension-`d` optimal constant

`C_fd(d)=sup_(U in X_d, Q_R(U)>0) q_U(w)/Q_R(U)`.             `(FDA9)`

Equations `(FDA5)` show that `C_fd(d)<infinity` is precisely a global
Lipschitz error bound

`||Psi_d(U)||_2 <= K_d ||Phi_d(U)||_2`.                       `(FDA10)`

Thus zero-set containment is not the missing assertion.  The missing
assertion is its linear metric strengthening.

## 2. A power-law bound always exists in fixed dimension

**Proposition 1 (fixed-dimensional Holder bound).**  Under `(FDA6)`, for
every fixed `d` there are an integer `N_d>=1` and a constant `A_d<infinity`
such that

`q_U(w)^(N_d) <= A_d Q_R(U)` for every `U in X_d`.             `(FDA11)`

**Proof.**  The functions `Q_R` and `q_U(w)` are nonnegative continuous
semialgebraic functions on the compact semialgebraic set `X_d`.  Their zero
sets satisfy

`Z(Q_R) subset Z(q_w)`                                       `(FDA12)`

by `(FDA8)`.  The semialgebraic Lojasiewicz inequality on a compact set
applied to `(FDA12)` gives `(FDA11)`.  End proof.

This is a genuine uniform statement inside each fixed dimension, but it is
not enough for TRUE.  An exponent `N_d>1` permits

`Q_R(U_n)=o(q_(U_n)(w))`,                                    `(FDA13)`

which is exactly what the desired linear bound forbids.

## 3. Regular exact solutions already have the linear bound

Let

`Z_d={U in X_d:Phi_d(U)=0}`.                                 `(FDA14)`

**Proposition 2 (constant-rank points are harmless).**  Let `U_0 in Z_d`.
If the differential of `Phi_d` has constant rank on a neighborhood of
`U_0` in `X_d`, then there are a neighborhood `V` of `U_0` and a finite
constant `K_(U_0)` such that

`||Psi_d(U)||_2 <= K_(U_0)||Phi_d(U)||_2`, `U in V`.          `(FDA15)`

**Proof.**  Apply the constant-rank theorem to `Phi_d`.  After smooth local
coordinate changes in source and target, `Phi_d` is the projection

`(y,z) |-> (y,0)`.                                           `(FDA16)`

The zero-set containment `(FDA8)` says that every coordinate of `Psi_d`
vanishes when `y=0`.  The coordinatewise fundamental theorem of calculus
therefore writes

`Psi_d(y,z)=sum_j y_j A_j(y,z)`                              `(FDA17)`

for continuous, in fact smooth, matrix-valued functions `A_j`.  Shrinking
the coordinate neighborhood makes the `A_j` bounded.  Norm equivalence
under the two local coordinate changes now gives `(FDA15)`.  End proof.

**Corollary 3.**  If every point of `Z_d` has a neighborhood on which
`Phi_d` has constant rank, then `C_fd(d)<infinity`.

**Proof.**  Proposition 2 and compactness of `Z_d` give the estimate on a
neighborhood of `Z_d`.  On the compact complement of a smaller neighborhood,
`Q_R` has a positive minimum while `q_U(w)<=1`.  Combining the two estimates
gives `(FDA10)` globally.  End proof.

Thus a fixed-dimensional failure cannot occur at a regular projective
representation stratum.  It must accumulate at a singular exact solution
of the relator-scalar equations.

## 4. The exact bad-arc criterion

**Proposition 4 (curve criterion).**  For a fixed `d`, the following are
equivalent.

1. `C_fd(d)=infinity`.
2. There are `U_0 in Z_d` and a nonconstant semialgebraic arc
   `U:(0,epsilon)->X_d`, with `U(t)->U_0`, such that

   `Q_R(U(t))>0`, `q_(U(t))(w)>0`,
   `Q_R(U(t))/q_(U(t))(w) -> 0`.                             `(FDA18)`

After a power reparametrization the arc may be taken real analytic.

**Proof.**  The implication `2=>1` is immediate.  Conversely, if the
quotient in `(FDA9)` is unbounded, compactness supplies an accumulation
point `U_0`.  Equation `(FDA8)` forces `U_0 in Z_d`.  Apply semialgebraic
curve selection to the graph of

`U |-> Q_R(U)/q_U(w)`                                       `(FDA19)`

on the semialgebraic locus where the denominator is positive.  This gives
`(FDA18)`.  Semialgebraic arcs admit a real-analytic parametrization after
a power substitution.  End proof.

The criterion can also be read as a real integral-closure test: the desired
linear estimate says that the coordinate germs of `Psi_d` are integrally
controlled by the ideal generated by the coordinate germs of `Phi_d`.
Zero-set containment places them only in the real radical.  Proposition 4
is the arc-valuative form of the gap between those two conditions.

## 5. One bad fixed-dimensional arc already proves FALSE

The previous criterion is not merely local geometry.

**Theorem 5 (bad-arc amplification).**  Under `(FDA6)`, if `(FDA18)` holds
in any fixed dimension, then there exists a hyperlinear nonsofic group.

**Proof.**  Choose `t_n->0`, set

`a_n=Q_R(U(t_n))`, `b_n=q_(U(t_n))(w)`,
`m_n=ceil(1/b_n)`.                                           `(FDA20)`

Since the limit lies in `Z_d`, `(FDA8)` gives `b_n->0`.  Take the tensor
power representation

`rho_n=pi_(U(t_n))^(tensor m_n)`.                            `(FDA21)`

Normalized characters multiply under tensor products, hence

`q_(rho_n)(g)=1-(1-q_(U(t_n))(g))^(m_n)`.                    `(FDA22)`

Therefore

`sum_(r in R)q_(rho_n)(r) <= m_n a_n -> 0`,                 `(FDA23)`

while

`q_(rho_n)(w)=1-(1-b_n)^(m_n) -> 1-exp(-1)>0`.              `(FDA24)`

Apply the conjugate double to `rho_n` and pass to a tracial matrix
ultraproduct.  Equation `(FDA23)` kills every relator, so the resulting
homomorphism factors through `P`.  Equation `(FDA24)` says that it retains
`w`.  Its image is hyperlinear.  It cannot be sofic, because `(FDA7)` says
that every homomorphism from `P` to a sofic group kills `w`.  End proof.

Thus proving the fixed-dimensional linear estimate is logically necessary
for TRUE.  Conversely, finding one singular arc with relator defect of
higher order than witness defect would solve the main problem in the FALSE
direction.

## 6. The remaining dichotomy

Let

`C_fd=sup_(d>=1) C_fd(d)`.                                   `(FDA25)`

Combining the preceding results gives the exact division:

* **singular finite-dimensional obstruction:** some `C_fd(d)` is infinite;
  equivalently, Proposition 4 supplies a bad arc, and Theorem 5 proves
  FALSE;
* **dimension-uniform obstruction:** every `C_fd(d)` is finite, but these
  constants are unbounded as `d->infinity`.

At regular exact projective solutions neither obstruction is present
locally.  The TRUE theorem therefore cannot fail through an isolated smooth
finite-dimensional solution.  It requires either nonlinear singular
projective deformation or deterioration across growing dimensions.

This is the theorem-shaped target for subsequent work: first analyze the
singular strata of the relator-scalar representation varieties; if they all
satisfy the linear arc criterion, seek a dimension-independent form of that
estimate.  More prime farming in one selected projective `SL_3(Z)` family
does not address either quantifier by itself.
