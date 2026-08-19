# Deck symmetry forbids microscopic subgroup-mean carry energy

Date: 2026-08-11

## 1. Purpose

The exact support formula in `FALSE_CARRY_MEAN_SUPPORT_FORMULA.md` has an
immediate consequence for the regular-cover radical filling code.  In a
regular cover of one fixed finite presentation, every nonzero deck-invariant
discriminant subgroup has carry support of positive density.  Its uniform
mean carry energy is therefore linear in the number of relator coordinates,
not `o(m)`.

This rules out the present uniform-subgroup pruning hypothesis
`(PCE10)/(RFD28c)` for the deck-invariant filling codes used in
`FALSE_RADICAL_FILLING_DISCRIMINANT.md`.  It does not rule out choosing a
nonuniform set of low-energy classes correlated with marked-word energy.

## 2. Orbit lower bound

Let `Y` be a fixed finite presentation `2`-complex with `b_2>0` oriented
two-cells.  Let

`Y_n->Y`                                               `(RCN1)`

be a finite regular cover of degree `d_n`, with deck group `G_n`.  Its set
of two-cells is a disjoint union of `b_2` free transitive `G_n`-orbits, so

`m_n=b_2 d_n`.                                        `(RCN2)`

Use the cellular basis to identify the ambient carry lattice with
`Lambda_n=Z^(m_n)`.  Let

`C_n<=D_(K,n)`                                        `(RCN3)`

be a nonzero `G_n`-invariant subgroup.  Discriminant gluing and the ambient
torus embedding give the equivariant injection

`theta_n:C_n->(R/Z)^(m_n)`.                           `(RCN4)`

For a coordinate `e`, write `theta_(n,e)` for the corresponding character
of `C_n`, and define

`S_n={e:theta_(n,e) is nontrivial}`.                  `(RCN5)`

**Theorem 1 (deck-orbit support gap).**  If `C_n!=0`, then

`|S_n|>=d_n=m_n/b_2`.                                 `(RCN6)`

More exactly, the order of the coordinate character is constant along each
deck orbit.  If `o_(n,t)` is that order on the lifts of the `t`-th base
two-cell, then

`(1/|C_n|)sum_(c in C_n)delta_n(c)^2`
` =d_n sum_(t=1)^b_2 nu(o_(n,t)),`                    `(RCN6a)`

and therefore

`(1/m_n)avg_(c in C_n)delta_n(c)^2`
` =(1/b_2)sum_(t=1)^b_2 nu(o_(n,t)).`                 `(RCN6b)`

Consequently its exact uniform mean carry energy satisfies

`(1/|C_n|)sum_(c in C_n)delta_n(c)^2`
` >=(2/(27b_2))m_n`.                                  `(RCN7)`

**Proof.**  Equivariance of `(RCN4)` and invariance of `C_n` imply that
`S_n` is `G_n`-invariant.  Indeed, if the character at `e` is nontrivial,
then the character at `g e` is its precomposition with the automorphism
`c |-> g^(-1)c` of `C_n`, and is also nontrivial.  Precomposition by an
automorphism also preserves the image order, proving constancy on each
orbit.  The coordinate-order formula `(CMS12)` now gives `(RCN6a)`, and
`(RCN2)` gives `(RCN6b)`.

The map `(RCN4)` is injective, so `C_n!=0` implies `S_n` is nonempty.  But
every nonempty `G_n`-invariant set of two-cells contains a full free deck
orbit, of cardinality `d_n`.  This proves `(RCN6)`.  Apply the lower bound
`(CMS18)` to get

`avg_C delta_n^2>=(2/27)|S_n|`
`                 >=(2/(27b_2))m_n`,                 `(RCN8)`

which is `(RCN7)`.  End proof.

The same proof applies when the phase table has any fixed finite number
`b` of ambient coordinate types over each sheet: replace `b_2` by `b`.

## 3. Consequences for the radical filling code

The regular radical filling code

`C_(w,X_n)=<c_(w,x):x in X_n>`                       `(RCN9)`

is deck invariant by construction.  The nonisotropy hypothesis needed to
retain the radical word forces it to be nonzero.  Theorem 1 therefore shows:

**Corollary 2.**  For regular covers of a fixed finite presentation, a
nonzero radical filling code can never satisfy

`avg_(c in C_(w,X_n))delta_n(c)^2=o(m_n)`.            `(RCN10)`

Hence the sufficient criteria `(PCE10)`, `(RFD28c)`, and their stronger
cycle/range-radius versions cannot certify FALSE in this deck-invariant
uniform-subgroup form.

This also explains why splitting the code as `C_n=P_n+Q_n` cannot repair
the issue.  The paired estimate `(PCE18)` is an upper bound which would
imply `(RCN10)`; Theorem 1 proves that no such microscopic upper bound is
possible for a nonzero invariant sum.

## 4. What remains open

The obstruction concerns **uniform averaging over an invariant subgroup**,
not individual discriminant classes.  A viable FALSE argument may still:

1. find a non-invariant or nonuniform family of classes with microscopic
   carry energy and macroscopic marked-word energy;
2. prove that low-energy classes and nontrivial word characters are
   positively correlated, rather than using subgroup character
   orthogonality followed by Markov pruning;
3. use chart families in which the number of ambient coordinate orbits
   tends to infinity, so one deck orbit has vanishing relative size; or
4. abandon the regular-cover phase ansatz.

The first option now has an exact two-torsion implementation.  If a binary
generator parametrization has maximum carry-row degree `a_n` and a positive
fraction of marked-word rows have degree at least `b_n`, then
`a_n/b_n->0` proves FALSE by sparse Bernoulli sampling; see
`FALSE_BERNOULLI_CARRY_INCIDENCE.md`.

Thus the next finite statistic is not the uniform mean `(PCE10)`.  It is the
joint distribution

`c |-> (delta_n(c)^2, mu_(w,n)(c)^2)`                 `(RCN11)`

on the radical filling code, with enough information to isolate a
low-carry/high-word tail despite the linear uniform mean.
