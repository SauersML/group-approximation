# A failed TRUE transfer has a one-witness transitive subgroup test

Date: 2026-08-11

## Purpose

The positive-loss theorem in `NOTEPAD.md` allows finitely many relation
words and finitely many outside witnesses, and quantifies over arbitrary
finite actions.  The finite-presentation radical localization later in the
same file reduces qualitative failure to one outside witness.  Combining
those two results with the orbit decomposition of a finite action gives a
sharper exact endpoint:

> if a hyperlinear group is not sofic, one weighted test with one outside
> word has a positive gap on every finite-index subgroup of a free group,
> while finite-dimensional unitary characters have loss tending to zero.

This is the normal-Dirac version of a subgroup test.  It does not prove that
the gap is impossible, but it removes disjoint unions and multiple witnesses
from the remaining theorem.

## Losses decompose over transitive orbits

Let `F` be a finitely generated free group, let `R subset F` be finite, let
`w in F`, and choose weights

`alpha_r>=0`, `beta>=0`,
`sum_(r in R) alpha_r+beta=1`.                         `(WTL1)`

For a nonempty finite `F`-action `rho` define

`L_(alpha,beta)(rho)`
` =sum_(r in R) alpha_r(1-chi_rho(r))+beta chi_rho(w)`, `(WTL2)`

where `chi_rho(g)` is the fraction of points fixed by `g`.

**Proposition 1 (transitive reduction).**

`inf_(rho finite F-action) L_(alpha,beta)(rho)`
` =inf_([F:H]<infinity) L_(alpha,beta)(F/H)`.          `(WTL3)`

Here `F/H` denotes the transitive left-coset action.  Equivalently, every
uniform lower bound for `(WTL2)` on transitive finite actions holds with the
same constant on all finite actions.

**Proof.**  Decompose the carrier of `rho` into its nonempty transitive
orbits,

`X=disjointUnion_(i=1)^k X_i`, `|X_i|=n_i`.           `(WTL4)`

For every `g in F`, fixed points decompose over the orbits, so

`chi_rho(g)=sum_i (n_i/|X|) chi_(X_i)(g)`.            `(WTL5)`

The loss `(WTL2)` is affine in the character.  Therefore

`L_(alpha,beta)(rho)`
` =sum_i (n_i/|X|)L_(alpha,beta)(X_i)`.               `(WTL6)`

Every `X_i` is isomorphic to `F/H_i` for a finite-index subgroup `H_i`.
Thus the loss of `rho` is at least the infimum on the right of `(WTL3)`.
The reverse inequality is immediate because every transitive action is a
finite action.  End proof.

## Exact finite-index-subgroup formula

For a finite-index subgroup `H<=F`, a coset `xH` is fixed by `g` precisely
when

`x^(-1) g x in H`.                                    `(WTL7)`

Consequently Proposition 1 turns `(WTL2)` into the explicit Boolean
subgroup test

`L_(alpha,beta)(F/H)`
` =E_(xH uniform in F/H)[ ell_(alpha,beta)(xHx^(-1)) ]`, `(WTL8)`

where

`ell_(alpha,beta)(K)`
` =sum_(r in R) alpha_r 1_(r notin K)+beta 1_(w in K)`. `(WTL9)`

The expression is well defined on cosets: replacing `x` by `xh`, with
`h in H`, does not change the conjugate subgroup `xHx^(-1)` after the
corresponding convention is fixed.  Directly from `(WTL7)`, one may also
write the unambiguous formula

`L_(alpha,beta)(F/H)`
` =1/[F:H] sum_(xH in F/H)`
`   (sum_r alpha_r 1_(x^(-1)rx notin H)`
`                    +beta 1_(x^(-1)wx in H)).`       `(WTL10)`

Thus the classical optimization ranges only over finite-index subgroups;
the conjugacy averaging is forced by choosing a uniform root in the coset
action.  If `C=core_F(H)`, then `(WTL10)` factors through the finite quotient
`F/C` and the subgroup `H/C`.  Equivalently, the infimum in `(WTL3)` ranges
over pairs

`Q a finite quotient of F`, `J<=Q`,                   `(WTL11)`

using the quasiregular action `Q/J`.  Restricting to regular actions
`J={1}` would be an unjustified strengthening.

## One-witness certificate for a counterexample

**Theorem 2 (one-witness transitive certificate).**  The following are
equivalent.

1. There exists a hyperlinear nonsofic group.
2. There exist a finitely generated free group `F`, a normal subgroup
   `N normal F`, a finite set `R subset N`, one word `w in F minus N`,
   weights as in `(WTL1)`, and `epsilon>0` such that

   `L_(alpha,beta)(F/H)>=epsilon`                     `(WTL12)`

   for every finite-index subgroup `H<=F`, while there are normalized
   finite-dimensional characters `chi_n` with

   `chi_n -> 1_N` pointwise.                           `(WTL13)`

In every certificate `(WTL12)`, necessarily `beta>0`.

**Proof.**  Suppose first that `Gamma=F/N` is hyperlinear and nonsofic.  The
single-witness reduction `(FPR1)--(FPR4)` in `NOTEPAD.md` gives finite
`R subset N` and one `w outside N` for which no sequence of finite actions
can make all relation deficits and the fixed fraction of `w` tend to zero.
Equivalently,

`inf_rho max({1-chi_rho(r):r in R} union {chi_rho(w)})>0`; `(WTL14)`

otherwise actions with maximum loss below `1/n` would give the forbidden
sequence.  Apply the positive-certificate minimax theorem
`(PLC1)--(PLC5)` to the coordinates `R disjointUnion {w}`.  It supplies
weights and `epsilon>0` such that `(WTL2)` is at least `epsilon` for every
finite action.  Proposition 1 makes this equivalent to `(WTL12)`.
Hyperlinearity gives `(WTL13)` by the normal-indicator characterization
`(NIR1)--(NIR3)`.

The weight `beta` cannot vanish: the one-point trivial action has
`chi(r)=1` for every `r`, and would make `(WTL2)` zero if `beta=0`.

Conversely, `(WTL13)` says that `F/N` is hyperlinear.  If it were sofic,
finite actions with characters converging to `1_N` would exist.  Their
losses in `(WTL2)` would converge to zero because `R subset N` and
`w outside N`, contradicting Proposition 1 and `(WTL12)`.  Thus `F/N` is
not sofic.  End proof.

The unitary zero-loss side can be made nonnegative without changing the
statement.  If `psi_n(g)=|chi_n(g)|^2`, then `psi_n` is again a normalized
finite-dimensional character and

`sum_r alpha_r(1-psi_n(r))+beta psi_n(w) -> 0`.        `(WTL15)`

Hence Theorem 2 is exactly a one-witness integrality-gap statement between
finite-dimensional characters and finite quasiregular actions.

## Real weights can be replaced by one uniform finite test

**Proposition 3 (rational and uniform certificate).**  In Theorem 2 the
weights may be chosen rational.  After clearing denominators, there are a
positive integer `M`, a multiset of relation words

`(r_1,...,r_a)`, with every `r_i in N`,                    `(WTL16)`

and a positive integer `b`, with `a+b=M`, such that every finite-index
`H<=F` satisfies

`1/M E_(xH in F/H)[`
` sum_(i=1)^a 1_(x^(-1)r_i x notin H)`
` +b 1_(x^(-1)w x in H)] >=epsilon'`                   `(WTL17)`

for some `epsilon'>0`.  The finite-dimensional unitary losses for the same
uniform multiset tend to zero.

**Proof.**  Start with weights and gap `epsilon` from Theorem 2.  Since the
weight simplex is finite-dimensional, choose a rational probability vector
`(alpha'_r,beta')` with

`sum_r |alpha'_r-alpha_r|+|beta'-beta|<epsilon/2`.     `(WTL18)`

Every loss coordinate lies in `[0,1]`, so replacing the weights changes the
value of the loss on any action by less than `epsilon/2`.  The new classical
gap is therefore at least `epsilon'=epsilon/2`.  Choose the approximation
close enough that `beta'>0`, which is possible because Theorem 2 gives
`beta>0`.  Clear a common denominator `M`, repeat each relation word
`M alpha'_r` times, and take `b=M beta'` copies of the single witness
coordinate.  Formula `(WTL10)` becomes `(WTL17)`.  The unitary loss is the
same rational linear combination, so `(WTL15)` still makes it tend to zero.
End proof.

Thus a failed TRUE implication would already produce a finite randomized
test with no real parameters: choose uniformly among `M` slots; a relation
slot rejects when the sampled rooted subgroup omits its conjugated relator,
and one of the `b` witness slots rejects when it contains the conjugated
witness.  Every finite Schreier model has rejection probability at least
`epsilon'`, whereas the nonnegative matrix characters have asymptotic loss
zero.

## Finite-presentation form and the remaining gate

Put

`P=<generators(F) | R>`.                              `(WTL19)`

The radical-localization theorem `(FPR5)--(FPR12)` says that the image of
`w` lies in `Rad_sof(P)` but survives in the hyperlinear quotient `F/N`.
Theorem 2 adds quantitative content: membership in the sofic radical is
witnessed by one positive quasiregular-character inequality `(WTL12)`.

This identifies three facts that a universal TRUE proof is allowed to use:

1. the target character is the indicator of a **normal** subgroup;
2. only one outside word is required; and
3. the classical adversaries are finite quotient/subgroup pairs `(Q,J)`,
   not arbitrary convex combinations after Proposition 1.

It also fixes the boundary of the reduction.  The conjugacy average in
`(WTL10)` cannot be replaced by pointwise membership in `H`, and the
subgroup `J` in `(WTL11)` cannot be discarded.  Proving that the unitary
zero-loss sequence `(WTL15)` forces some finite-index subgroup with small
loss `(WTL10)` is precisely the remaining subgroup-test rounding theorem;
none of the reductions above supplies it.
