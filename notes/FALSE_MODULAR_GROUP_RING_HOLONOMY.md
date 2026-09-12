# Radical holonomy is a modular group-ring socle calculation

Date: 2026-08-11

## 1. Purpose

`FALSE_TRANSFER_HOLONOMY_CERTIFICATE.md` reduces the surviving FALSE route
to

`A_X a=Jv mod q`, `h=<a,b_(w,x)> mod q`.                           `(MGR1)`

For a regular cover this is not an unstructured matrix problem.  It is one
linear equation over the modular group ring of the deck group.  At a prime
dividing the cover degree, the constant lift is the group-ring norm element,
which is square-zero.  Thus the only still-live sector is precisely the
nonsemisimple modular block containing the trivial representation.

This note records that reduction and gives a Fox-derivative recipe for the
holonomy.  It applies in particular to the explicit finitely presented
Kun--Thom radical double in `FALSE_EXPLICIT_FP_RADICAL_DOUBLE.md`.

**Closure update for that example.**  The general group-ring reduction
remains live, but the specific `SL_d(Z)*SL_d(Z)` quotient tower in Section 6
is closed by `FALSE_FIXED_KERNEL_COVER_NO_GO.md`: the marked word lies in
the commutator subgroup of the fixed quotient kernel, which supplies a
cover-independent filling.  Consequently the Fox functional in `(MGR25)`
is the reduction of a fixed integral functional and cannot have unbounded
centered slope.

## 2. The equivariant presentation matrix

Fix a finite presentation

`H=<s_1,...,s_e | r_1,...,r_f>`                                    `(MGR2)`

and an epimorphism `theta:H->T` to a finite group.  Let `P_T->P` be the
corresponding connected regular cover.  After choosing the identity lifts
of the cells, its cellular modules are

`C^1(P_T,Z)=Z[T]^e`, `C^2(P_T,Z)=Z[T]^f`.                          `(MGR3)`

The coboundary is a matrix

`A_T:Z[T]^e->Z[T]^f`                                               `(MGR4)`

obtained from the Fox Jacobian of the relators, specialized by `theta`
(with the harmless transpose/involution dictated by the left-versus-right
module convention).

Write

`N_T=sum_(t in T)t in Z[T]`.                                      `(MGR5)`

Under `(MGR3)`, the constant lift of a base relator vector `v in Z^f` is

`Jv=N_T v`.                                                       `(MGR6)`

Consequently the transfer-holonomy equation is exactly

`A_T a=N_T v in (Z/q)[T]^f`.                                     `(MGR7)`

This proves that its solvability is invariant under all changes of cellular
bases and can be tested directly from the specialized Fox matrix, without
constructing the integral cycle lattice of the cover.

## 3. The modular norm sector

The norm element satisfies

`tN_T=N_Tt=N_T`, `N_T^2=|T|N_T`.                                  `(MGR8)`

**Theorem 1 (square-zero norm sector).**  Let `p` be a prime dividing
`|T|`.  In `F_p[T]`, the nonzero norm element `N_T` is central, is killed by
the augmentation ideal, and satisfies

`N_T^2=0`.                                                        `(MGR9)`

If `T` is a `p`-group, `F_p[T]` is local and its socle is the
one-dimensional space `F_p N_T`.  Hence `(MGR7)` with `q=p` asks exactly
whether the socle vector `N_Tv` belongs to `im(A_T)`.

**Proof.**  The identities in `(MGR8)` give centrality, annihilation by
every `t-1`, and square-zero because `p` divides `|T|`.  For a finite
`p`-group, the augmentation ideal is the Jacobson radical of `F_p[T]`.
Its common annihilator is the invariant line, spanned by `N_T`; this is the
socle.  End proof.

This explains the degree screen in the transfer theorem.  A sequence with a
fixed primitive `v` and `q->infinity` cannot live in semisimple
characteristics disjoint from the cover degrees: the necessary congruence

`q divides |T| ||v||^2`                                           `(MGR10)`

forces the growing prime-power part of `q` into the modular norm sector.
The obstruction is therefore not ordinary Fourier analysis on `T`; it is a
modular extension/socle problem.

## 4. Fox formula for the marked radical phase

Let `w` be a word with `theta(w)=1`.  Its lifted edge cycle based at the
identity is the specialized Fox vector

`b_w=(theta(partial w/partial s_i))_(i=1)^e in Z[T]^e`,            `(MGR11)`

again up to the same fixed left/right involution convention as `(MGR4)`.
Let `[1]` denote coefficient extraction at the identity of `T` and use the
standard coefficient pairing on `Z[T]^e`.

**Theorem 2 (group-ring holonomy formula).**  If

`A_Ta=N_Tv mod q`,                                                 `(MGR12)`

then the scalar phase of `w` in the associated monomial microstate is

`exp(-2 pi i h/q)`,
`h=[1]<a,b_w> mod q`.                                              `(MGR13)`

If `w in Rad_sof(H)`, the residue in `(MGR13)` is independent of the
chosen solution and of the base vertex.  Equivalently it is the canonical
linear functional

`Hol_(w,T,q):N_T(K_1) intersect im(A_T)->Z/q`                       `(MGR14)`

from `FALSE_TRANSFER_HOLONOMY_CERTIFICATE.md`, now written entirely over
`(Z/q)[T]`.

**Proof.**  The Fox identity says that `(MGR11)` is precisely the cellular
chain obtained by reading `w` in the cover.  Pairing its edge occurrences
with the phase cochain `-a/q` gives `(MGR13)`.  The radical argument in
Lemma 2 of the transfer-holonomy note kills the evaluation of every
homogeneous solution of `A_Ta=0`; it also makes the evaluations at all deck
translates equal.  End proof.

Thus a finite computation needs only:

1. specialize the fixed Fox matrix and Fox vector in a finite quotient `T`;
2. solve the socle equation `(MGR12)`; and
3. test whether `(MGR13)` has order comparable with `q`.

## 5. Central-deformation interpretation

The modular equation has an equivalent group-theoretic interpretation
which is useful independently of the Fox calculation.  For
`v=(v_1,...,v_f) in Z^f`, define the central relator deformation

`Htilde_(v,q)=<s_1,...,s_e,z | z^q=1, [z,s_i]=1,`
`                              r_j=z^(-v_j)>`.                     `(MGR15)`

Here the sign agrees with the phase convention `x=-a/q` in the transfer
note.

**Theorem 3 (finite central-deformation equivalence).**  A solution of

`A_Ta=N_Tv mod q`                                                  `(MGR16)`

is equivalent to a homomorphism

`rho_a:Htilde_(v,q)->mu_q^T semidirect T`                          `(MGR17)`

whose permutation part is the regular action of `T` and for which
`rho_a(z)=exp(2 pi i/q)I`.  Under this homomorphism the word lift defined by
the same word in the `s_i` satisfies

`rho_a(w)=rho_a(z)^(-h)`,
`h=[1]<a,b_w> mod q`.                                              `(MGR18)`

**Proof.**  Put the edge phase cochain `x=-a/q` on the regular `T`-chart.
The cellular word calculation gives

`A_Tx=integer cochain-(1/q)N_Tv`.                                 `(MGR19)`

Thus the monomial matrices attached to the generators satisfy every
deformed relator in `(MGR15)` exactly and send `z` to the displayed scalar.
Their image lies in the finite monomial group `mu_q^T semidirect T`, which
gives `(MGR17)`.  Conversely, read the `q`-th-root diagonal entries of such
a monomial homomorphism as an edge cochain.  Its relator equations are
exactly `(MGR16)`, up to the fixed left/right convention.  Finally the Fox
word calculation `(MGR13)` gives `(MGR18)`.  End proof.

There is no contradiction with `w in Rad_sof(H)`: `(MGR17)` is a finite
representation of the varying central deformation `Htilde_(v,q)`, not of
`H`.  The crucial asymptotic mismatch is now completely visible.  The
relator deformation has size `O(||v||/q)`, while the lifted radical word has
displacement

`|exp(2 pi i h/q)-1|`.                                             `(MGR20)`

Consequently the transfer-holonomy FALSE certificate is equivalently a
sequence of finite quotients of `(MGR15)` in which

`||v||/q->0`, `dist(h/q,Z)>=epsilon>0`.                            `(MGR21)`

After tensor amplification, the second requirement can be weakened
strictly.  If `H_q(h)=dist(h,qZ)` is the centered residue, Theorem 3a of
`FALSE_TRANSFER_HOLONOMY_CERTIFICATE.md` only requires

`H_q(h)/||v||->infinity`.                                          `(MGR21a)`

Indeed the radical-character to total-relator-character ratio is at least

`(4/pi^2) H_q(h)^2/||v||^2`.                                      `(MGR21b)`

Thus the central deformation need not send `w` to a root of unity a fixed
angular distance from `1`.  Its exponent only has to grow relative to the
integer relator-deformation vector; conjugate doubling and tensor powers
then create the macroscopic phase.

This is an exact finite-quotient formulation of the remaining problem,
with no ultraproduct or lattice terminology in its hypotheses.

## 6. Application to the explicit radical double

For

`D=(EL_r(R) semidirect SL_d(Z)) *_(EL_r(R_+))`
`  (EL_r(R) semidirect SL_d(Z))`                                  `(MGR22)`

from `FALSE_EXPLICIT_FP_RADICAL_DOUBLE.md`, take finite deck quotients of

`SL_d(Z)*SL_d(Z)`.                                                 `(MGR23)`

The explicit radical word is

`w=i_2(e_12(x_1^(-1)))i_1(e_12(x_1^(-1)))^(-1)`.                  `(MGR24)`

Choose congruence quotients whose orders are divisible by a prime `p` and
reduce the fixed Fox data modulo `p`.  The complete remaining finite test is

`N_Tv in im(A_T:F_p[T]^e->F_p[T]^f)`,
`[1]<a,b_w> !=0`.                                                  `(MGR25)`

For a sequence with primes or prime powers tending to infinity, the
quantitative version only requires the centered second residue to grow
faster than `||v||`; it may be `o(q)`.  If `(MGR25)` holds with fixed `p`,
it is still a genuine nonzero-holonomy certificate, but by itself does not
make the normalized relator defect tend to zero.

For this particular tower, however, the perfect-kernel no-go gives a fixed
integral filling `z_0` and the exact identity

`[1]<a,b_w>=<v,z_0> mod q`.                                      `(MGR26)`

The centered value is at most `||v||||z_0||`, so the required slope cannot
diverge.  Thus `(MGR25)` is useful only as a finite diagnostic here, not as
an asymptotic counterexample route.

## 7. Status

The general reduction is exact but not a final FALSE proof.  Its content is
that a transfer class is a square-zero norm/socle class of a modular group
algebra.  This eliminates semisimple character searches.  The previously
stated target

> Find an unbounded modular quotient tower of `(MGR23)` for which the norm
> socle class `N_Tv` is a Fox coboundary and its canonical radical Fox
> functional has centered order growing faster than `||v||`.

is impossible for the explicit tower `(MGR23)` by `(MGR26)`.  It remains a
valid finite algebraic target only for quotient towers whose kernels do not
admit one common commutator filling of the marked radical word.
