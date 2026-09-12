# The TRUE domination gap is purely dimension-uniform

Date: 2026-08-11

## Purpose

`TRUE_RADICAL_DOMINATION_CONSTANTS.md` reduces the assertion that every
hyperlinear group is sofic to one comparison.  For a finite presentation

`P=<s_1,...,s_k | R>`

and a word `w`, finiteness of the permutation domination constant must imply
finiteness of the finite-dimensional character domination constant.

This note proves that the comparison already holds in every fixed matrix
dimension.  In a fixed dimension it is a real-algebraic Lipschitz
error-bound problem.  Constant-rank exact projective solutions satisfy that
bound directly.  At a singular solution, any hypothetical bad arc can be
truncated at its first nonzero witness jet; the resulting exact target is a
finitely generated complex linear group and hence sofic, contradicting the
sofic-radical hypothesis.

Consequently the only remaining obstruction is degeneration as the matrix
dimension tends to infinity.

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
representation stratum.  The next sections show that jet truncation also
rules it out at singular exact solutions.

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

## 5. Jet truncation eliminates every bad fixed-dimensional arc

The previous criterion looks like a possible singular obstruction, but the
group structure rules it out.

**Theorem 5 (fixed-dimensional linear domination).**  Under `(FDA6)`,

`C_fd(d)<infinity for every fixed d`.                         `(FDA20)`

**Proof.**  Suppose instead that `C_fd(d)=infinity`.  Proposition 4 gives a
semialgebraic arc satisfying `(FDA18)`.  After replacing its parameter by a
positive power, write all its matrix entries as convergent power series in
`t`.  Put

`A_g(t)=hat pi_(U(t))(g) in GL_(d^2)(C{t})`.                 `(FDA21)`

For a nonzero matrix power series `M(t)`, let `ord(M)` be the least order of
one of its entries.  Since normalized Hilbert--Schmidt norm squared is a sum
of entrywise absolute squares along the real parameter,

`ord(q_(U(t))(g))=2 ord(A_g(t)-1)`                           `(FDA22)`

whenever `A_g(t)-1` is not identically zero.  There is no leading-term
cancellation in this identity.

Let

`b=ord(A_w(t)-1)`.                                           `(FDA23)`

The witness is nontrivial on the punctured arc, so `b<infinity`.  Condition
`(FDA18)` and `(FDA22)` imply

`ord(A_r(t)-1)>b for every r in R`.                          `(FDA24)`

Now reduce all matrices modulo `t^(b+1)`.  The generator matrices remain
invertible, every relator becomes exactly the identity, and the witness does
not:

`bar A_r=1`, `r in R`,
`bar A_w!=1`                                                 `(FDA25)`

in

`GL_(d^2)(C{t}/(t^(b+1)))`.                                  `(FDA26)`

Thus the assignment `s_i |-> bar A_(s_i)` defines a homomorphism

`P -> GL_(d^2)(C{t}/(t^(b+1)))`                              `(FDA27)`

which retains `w`.

The truncated coefficient algebra in `(FDA26)` is a complex vector space of
dimension `b+1`.  Its left regular action embeds the target group faithfully
into

`GL_(d^2(b+1))(C)`.                                          `(FDA28)`

The image of the finitely generated group `P` under `(FDA27)` is therefore
a finitely generated complex linear group.  By Malcev's theorem it is
residually finite, hence sofic.  But `(FDA7)` says that every homomorphism
from `P` to a sofic group kills `w`, contradicting `(FDA25)`.  Therefore
`C_fd(d)<infinity`.  End proof.

The proof is stronger than tensor amplification.  A bad arc would not only
produce an asymptotic matrix model: its first nonzero jet would already give
an exact sofic quotient retaining the radical word.

## 6. The sole remaining obstruction

Let

`C_fd=sup_(d>=1) C_fd(d)`.                                   `(FDA29)`

Theorem 5 shows that every term in `(FDA29)` is finite.  Combining it with
the domination-constant characterization gives the sharpened remaining
problem:

`C_perm(P,R,w)<infinity`
`  ==>  sup_(d>=1) C_fd(d)<infinity`.                         `(FDA30)`

There is no exact finite-stage obstruction, no fixed-dimensional nonlinear
arc obstruction, and no singular-stratum exception.  If `(FDA30)` fails,
it is witnessed by dimensions `d_n->infinity` and representations `pi_n`
with

`Q_R(pi_n)>0`,
`q_(pi_n)(w)/Q_R(pi_n)->infinity`.                            `(FDA31)`

Tensor amplification then converts `(FDA31)` into the usual hyperlinear
nonsofic radical witness.  The unbounded growth of `d_n` is essential: every
bounded-dimensional subsequence is excluded by Theorem 5.

This is now the theorem-shaped TRUE target: make the fixed-dimensional
linear constants uniform in `d`.  More prime farming in one selected
projective `SL_3(Z)` family does not address that quantifier by itself.

## 7. Every fixed-dimensional constant is effectively computable

Theorem 5 also makes the remaining sequence completely explicit.

**Corollary 6 (effective algebraic constants).**  Given the finite words
`R,w` and a dimension `d`, under `(FDA6)` the number `C_fd(d)` is a finite
real-algebraic number and can be computed, in principle, by quantifier
elimination over real closed fields.

**Proof.**  Write every matrix variable in real and imaginary coordinates.
The equations defining `U(d)^k`, and the functions `Q_R` and `q_w`, have
rational coefficients.  For a real parameter `C`, the assertion

`C>=0 and q_U(w) <= C Q_R(U) for every U in U(d)^k`          `(FDA32)`

is a first-order formula over the real closed field with rational
coefficients.  Its set of solutions in `C` is therefore semialgebraic over
`Q`.  It is an upper ray, and it is nonempty by Theorem 5.  Its left endpoint
is exactly `C_fd(d)`.  A finite endpoint of a one-dimensional semialgebraic
set over `Q` is real algebraic, and real quantifier elimination computes its
defining algebraic data and isolating interval.  End proof.

Consequently the universal comparison `(FDA30)` is equivalent to boundedness
of the computable sequence of algebraic numbers

`C_fd(1), C_fd(2), C_fd(3), ...`.                            `(FDA33)`

The computation is not proposed as a practical algorithm: generic real
quantifier elimination is enormous even at small `d`.  Its conceptual role
is to show that no undecidable or infinitary ambiguity remains at an
individual dimension.  All difficulty is in a bound uniform over the
unbounded sequence `(FDA33)`.

## 8. One factorial matrix tower contains the whole obstruction

There is no need to range over unrelated dimension sequences.

**Proposition 7 (divisibility monotonicity).**  For all positive integers
`d,m`,

`C_fd(md)>=C_fd(d)`.                                         `(FDA34)`

Consequently

`sup_(d>=1) C_fd(d)=sup_(n>=1) C_fd(n!)`,                    `(FDA35)`

and the sequence on the right is nondecreasing.

**Proof.**  Given `pi:F_k->U(d)`, take the direct sum of `m` identical
copies.  Its normalized character is exactly the normalized character of
`pi`, so every quotient `q_pi(w)/Q_R(pi)` is reproduced in dimension `md`.
This proves `(FDA34)`.  Every `d` divides `n!` for all sufficiently large
`n`, giving `(FDA35)`; consecutive factorials divide one another, so their
constants are nondecreasing.  End proof.

Thus the last TRUE implication is equivalent to boundedness of the single
monotone computable sequence

`C_fd(1!), C_fd(2!), C_fd(3!), ...`.                          `(FDA36)`

Equivalently, all finite stages may be placed in the canonical divisibility
tower

`M_(1!) -> M_(2!) -> M_(3!) -> ...`                          `(FDA37)`

using block-diagonal repetition.  This does not itself supply compatible
witness tuples from one stage to the next; forcing such compatibility would
be another form of the missing dimension-uniform theorem.  It does show that
arbitrary prime factors or sporadic matrix sizes are not part of the
obstruction.
