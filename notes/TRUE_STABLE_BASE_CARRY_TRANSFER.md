# Permutation exactification plus carry repair kills radical phases

Date: 2026-08-11

## Purpose

`TRUE_EXACT_COVER_MONOMIAL_DISCRIMINANT.md` controls all phase orders once
the underlying permutation chart is an exact finite action of the presented
group.  A monomial hyperlinear table has only an approximate quotient action:
its permutation relators move few points, but need not be identities.

This note proves the quantitative bridge between those two settings.  Keep
the original phases while exactifying the permutation part, then apply
circle repair on the resulting exact chart.  The two errors compose with an
explicit estimate.  Consequently:

* sequencewise permutation stability plus uniform exact-chart carry repair
  rules out every monomial radical witness;
* no bounded phase exponent is required; and
* the remaining nonexact-chart obstruction is precisely failure of one of
  those two repairs at the required joint rate.

## 1. Setup

Let `F=F(S)` be the free group on a finite set `S`, let `R subset F` be
finite, and put

`P=F/normal_closure_F(R)`.                              `(SBC1)`

Fix `w in Rad_sof(P)`.  Let `X` be a nonempty finite set and let

`U:F->Mon(X)=T^X semidirect Sym(X)`                    `(SBC2)`

be a monomial unitary representation.  Write

`U(s)e_x=a_s(x)e_(rho(s)x)`                            `(SBC3)`

for its permutation part `rho:F->Sym(X)` and phase labels `a_s(x) in T`.
All matrix norms below are normalized Hilbert--Schmidt norms.

Suppose an exact finite `P`-action

`rhobar:F->Sym(X)`                                    `(SBC4)`

has been chosen on the same set.  Thus `rhobar(r)=1` for every `r in R`.
Keep the phase labels from `(SBC3)` and define

`Ubar(s)e_x=a_s(x)e_(rhobar(s)x)`.                    `(SBC5)`

The matrices `(SBC5)` extend uniquely to a representation of the free group,
but generally not of `P`: their relators are diagonal phase errors.

Define

`h(rho,rhobar)=sum_(s in S)d_Ham(rho(s),rhobar(s))`,  `(SBC6)`

`E_R(U)=sqrt(sum_(r in R)||U(r)-1||_2^2)`,            `(SBC7)`

`L_R=sqrt(sum_(r in R)ell(r)^2)`,                     `(SBC8)`

where `ell(g)` is displayed word length in `S union S^(-1)`.

Let `A_X` be the integral phase-relator matrix of the exact action
`rhobar`, and let `C_circ(A_X)` be its nonlinear circle-repair constant as
in `TRUE_NONLINEAR_DISCRIMINANT_REPAIR_FORMULA.md`.

## 2. Moving the permutation part

**Lemma 1 (phase-preserving permutation transfer).**  For every generator,

`||U(s)-Ubar(s)||_2^2`
` =2 d_Ham(rho(s),rhobar(s)).`                        `(SBC9)`

For every word `g in F`,

`||U(g)-Ubar(g)||_2`
` <=ell(g)sqrt(2 h(rho,rhobar)).`                     `(SBC10)`

Consequently

`sqrt(sum_(r in R)||Ubar(r)-1||_2^2)`
` <=E_R(U)+sqrt(2 h(rho,rhobar))L_R.`                 `(SBC11)`

**Proof.**  In one column, the two monomial generator matrices in
`(SBC3)` and `(SBC5)` have the same phase.  Their columns agree when the two
permutations agree and are orthogonal otherwise.  The squared column
distance is therefore zero or two, which proves `(SBC9)` after averaging.

Telescoping a word product and using unitary invariance of normalized
Hilbert--Schmidt norm bounds its difference by the sum of the generator
differences.  Every one is at most `sqrt(2h)`, proving `(SBC10)`.
For each relator, the triangle inequality gives

`||Ubar(r)-1||_2<=||U(r)-1||_2+ell(r)sqrt(2h).`       `(SBC12)`

Minkowski's inequality in the finite `ell_2(R)` sum proves `(SBC11)`.
End proof.

## 3. Repairing the transferred phases

Because `rhobar` is an exact `P`-action, every `Ubar(r)` is diagonal.  If
`theta` is a real phase lift, then

`||Ubar(r)-1||_2^2`
` =(1/|X|)sum_(x in X)`
`   |exp(2 pi i(A_Xtheta)_(x,r))-1|^2.`               `(SBC13)`

On `[-1/2,1/2]`,

`4 dist(t,Z)<=|exp(2 pi i t)-1|<=2 pi dist(t,Z)`.     `(SBC14)`

Thus `(SBC11)` bounds the additive circle defect of `theta`.  Repair it to
`theta_0 in ker(bar(A_X))`, and let

`V(s)e_x=exp(2 pi i theta_(0,s)(x))e_(rhobar(s)x).`   `(SBC15)`

Then `V` factors through `P` exactly.

**Theorem 2 (stable-base carry-transfer inequality).**  Put

`h=h(rho,rhobar)`, `C=C_circ(A_X)`.                  `(SBC16)`

Then

`||U(w)-1||_2`
` <=ell(w)sqrt(2h)`
`   +(pi/2)ell(w) C (E_R(U)+sqrt(2h)L_R).`            `(SBC17)`

**Proof.**  Equations `(SBC13)--(SBC14)` and `(SBC11)` give

`def_(A_X)(theta)`
` <=(1/4)(E_R(U)+sqrt(2h)L_R).`                      `(SBC18)`

By circle repair, `theta_0` may be chosen so that, up to an arbitrarily
small additive error,

`||theta-theta_0||_(1,T)`
` <=(C/4)(E_R(U)+sqrt(2h)L_R).`                      `(SBC19)`

The matrices `Ubar(s)` and `V(s)` have the same permutation part.  The
upper half of `(SBC14)`, summed over generators, yields

`sqrt(sum_(s in S)||Ubar(s)-V(s)||_2^2)`
` <=2 pi ||theta-theta_0||_(1,T).`                   `(SBC20)`

Telescoping the word `w` bounds `||Ubar(w)-V(w)||_2` by `ell(w)` times the
left side of `(SBC20)`.  Finally, the image of `V` lies in

`T^X semidirect Sym(X)`,                              `(SBC21)`

which is abelian-by-finite and hence amenable and sofic.  Since `V` factors
through `P` and `w in Rad_sof(P)`, one has

`V(w)=1`.                                             `(SBC22)`

Combine `(SBC10)` for `w`, `(SBC19)--(SBC22)`, and let the repair error tend
to zero.  This is exactly `(SBC17)`.  End proof.

The use of the sofic radical in `(SBC22)` is essential.  Circle repair makes
an exact monomial representation of `P`; it need not make every phase
trivial.

## 4. Sequence theorem

Let

`U_n:F->Mon(X_n)`                                     `(SBC23)`

be a sequence of finite monomial representations.  Let `rho_n` be their
permutation parts.  Suppose there are exact finite `P`-actions `rhobar_n`
on `X_n`, and put

`h_n=h(rho_n,rhobar_n)`, `C_n=C_circ(A_(X_n))`.       `(SBC24)`

**Corollary 3 (joint-rate criterion).**  If

`h_n->0`,
`C_n(E_R(U_n)+sqrt(h_n))->0`,                         `(SBC25)`

then

`||U_n(w)-1||_2->0`, `delta_(U_n)(w)->0`.             `(SBC26)`

In particular, `(SBC25)` holds if

`E_R(U_n)->0`, `h_n->0`, `sup_n C_n<infinity`.        `(SBC27)`

This follows immediately from `(SBC17)`.  Notice that the circle alphabets
and all phase orders may grow arbitrarily.

The permutation part is automatically an approximate `P`-action whenever
the unitary relator defects vanish.  Indeed, for every `g in F`,

`d_(rho_n)(g)<=delta_(U_n)(g)`,                       `(SBC28)`

because a moved basis point contributes exactly one to
`1-Re tr(U_n(g))`, while every fixed-point phase contributes a nonnegative
amount.  Also

`E_R(U_n)^2=2 sum_(r in R)delta_(U_n)(r).`            `(SBC29)`

Therefore qualitative permutation stability of the presentation supplies
`rhobar_n` with `h_n->0`.

**Corollary 4 (stable presentation plus uniform carries).**  Suppose:

1. `P` is permutation stable for the presentation `(SBC1)`: every sequence
   of finite permutation maps with relator Hamming defects tending to zero
   is generatorwise close to exact finite `P`-actions on the same sets; and
2. the exact finite `P`-actions have uniformly bounded circle-repair
   constants.

Then every monomial sequence with vanishing relator character defect kills
every `w in Rad_sof(P)` in normalized Hilbert--Schmidt norm.

**Proof.**  Equations `(SBC28)--(SBC29)` give an approximate permutation
action and `E_R(U_n)->0`.  Assumption 1 gives `h_n->0`; assumption 2 gives
`sup C_n<infinity`.  Apply Corollary 3.  End proof.

The same conclusion holds for flexible exactification, where an asymptotically
negligible number of points may be added or removed.

**Corollary 5 (flexible stable-base transfer).**  Suppose that for each `n`
there is a finite set `Z_n` containing relabelled copies of the original
model `X_n` and of an exact finite `P`-set `Y_n`.  Extend `U_n` to `Z_n` by
the identity on `Z_n minus X_n`, and extend the exact `P`-action on `Y_n` by
the trivial action on `Z_n minus Y_n`.  Assume

`|X_n|/|Z_n|->1`, `|Y_n|/|Z_n|->1`,                  `(SBC29a)`

and that the two extended permutation maps have generator Hamming distance
`h_n->0`.  If the exact extended charts have uniformly bounded circle-repair
constants and `E_R(U_n)->0`, then `(SBC26)` holds.

**Proof.**  On the common set `Z_n`, the extended monomial representation
`U_n^+` satisfies

`||U_n^+(g)-1||_2^2`
` =(|X_n|/|Z_n|)||U_n(g)-1||_2^2                    `(SBC29b)`

for every `g`: the added block is the identity.  Thus its relator defects
vanish.  Apply Corollary 3 on `Z_n`.  Equation `(SBC29b)` for `g=w`, together
with `|X_n|/|Z_n|->1`, transfers the conclusion back to `U_n`.  End proof.

Hence Corollary 4 remains valid with same-set permutation stability replaced
by flexible permutation stability with `o(|X_n|)` stabilization.  The
trivial added orbits cause no phase compatibility problem.

Using the exact carry formula, assumption 2 follows from

`inf_X sigma_+(A_X)>0`, `sup_X Theta(A_X)<infinity`.  `(SBC30)`

For a fixed property-`(T)` presentation, the first part of `(SBC30)` is the
universal Hodge gap already proved in
`TRUE_PROPERTY_T_LINEAR_COCYCLE_GAP.md`.  The integral carry bound is the
remaining nonlinear input.

## 5. Exact remaining boundary

The theorem separates the nonexact monomial problem into two independently
verifiable losses:

1. **base exactification:** find `rhobar_n` with `h_n->0`, or more generally
   with the joint rate in `(SBC25)`;
2. **phase repair:** bound `C_n`, equivalently the paired-discriminant carry
   geometry on the selected exact charts.

Neither condition follows from the other.  Generic permutation stability is
not known for the radical presentations relevant to the universal problem,
and real Hodge expansion alone does not bound integral carries.  The theorem
does prove that there is no third compatibility obstruction: the original
phases can be retained during exactification, and the two repairs compose by
the explicit inequality `(SBC17)`.

This still concerns monomial models.  A full TRUE proof must additionally
obtain a suitable common Cartan/monomial model from arbitrary
finite-dimensional characters, as isolated in
`TRUE_CARTAN_MONOMIAL_GATE.md`, or bypass monomialization altogether.
