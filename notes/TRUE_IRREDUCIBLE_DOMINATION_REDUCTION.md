# The matrix domination obstruction is irreducible

Date: 2026-08-11

## Purpose

`TRUE_RADICAL_DOMINATION_CONSTANTS.md` defines, for

`P=<s_1,...,s_k | R>`

and a word `w`, the finite-dimensional constant

`C_fd=sup_pi q_pi(w)/sum_(r in R)q_pi(r)`,
`q_pi(g)=1-|tr(pi(g))|^2`,                                  `(IDR1)`

where `pi:F_k->U(d)` ranges over all finite dimensions and all traces are
normalized.

This note removes reducibility, multiplicity, direct-sum variance, and the
absolute square from the remaining gate.  The constant `(IDR1)` is exactly
the supremum of an affine Hilbert--Schmidt defect ratio over irreducible
representations.  Moreover every bounded irreducible dimension has a finite
constant.  Thus a failure of TRUE must be witnessed by irreducible unitary
representations of dimensions tending to infinity.

## 1. The affine defect

For a finite-dimensional unitary representation `sigma` of `F_k`, put

`delta_sigma(g)=1-Re tr(sigma(g))`
`              =(1/2)||sigma(g)-1||_2^2`.                  `(IDR2)`

This defect is affine under direct sums with dimension weights.  Define

`K_irr=sup_(sigma irreducible)`
`  delta_sigma(w)/sum_(r in R)delta_sigma(r)`,               `(IDR3)`

where terms with zero denominator are omitted.  They cause no ambiguity
when `w in Rad_sof(P)`: zero relator defect means that `sigma` factors
through `P`; its finitely generated linear image is sofic and therefore
kills `w`.

## 2. Exact equality of the two constants

**Theorem 1 (irreducible reduction).**  If `w in Rad_sof(P)`, then

`C_fd=K_irr`.                                                `(IDR4)`

**Proof of `C_fd<=K_irr`.**  Let `pi:F_k->U(d)` and form its conjugate
double

`hat pi=pi tensor conjugate(pi)`.                            `(IDR5)`

Its normalized character is `|tr(pi(g))|^2`, so

`delta_(hat pi)(g)=q_pi(g)`.                                 `(IDR6)`

Decompose `hat pi` as a finite direct sum of irreducibles `sigma_j`, and
let `a_j` be their dimension weights.  By affinity of normalized trace,

`q_pi(g)=sum_j a_j delta_(sigma_j)(g)`.                      `(IDR7)`

Consequently the quotient in `(IDR1)` is a denominator-weighted average of
the irreducible quotients in `(IDR3)` and is at most `K_irr`.

**Proof of `K_irr<=C_fd`.**  Fix an irreducible
`sigma:F_k->U(e)`.  For `M>=1`, let

`rho_M=1^(direct sum M) direct sum sigma`,
`t_M=e/(M+e)`.                                               `(IDR8)`

Its normalized character is

`tr(rho_M(g))=1-t_M+t_M tr(sigma(g))`.                       `(IDR9)`

Therefore, exactly,

`q_(rho_M)(g)`
` =2t_M delta_sigma(g)-t_M^2|1-tr(sigma(g))|^2`.             `(IDR10)`

After division by `2t_M` and passage to `M->infinity`, the ratio for
`rho_M` in `(IDR1)` tends to the ratio for `sigma` in `(IDR3)`.  Taking the
supremum over `sigma` gives `K_irr<=C_fd`.  End proof.

The two operations in the proof are canonical:

* conjugate doubling changes the nonlinear phase-insensitive defect into an
  affine Hilbert--Schmidt defect;
* dilution by trivial blocks reverses that passage at the level of optimal
  ratios.

Thus neither phases nor reducible mixtures contribute an additional
obstruction.

## 3. Fixed irreducible dimensions are harmless

For `D>=1`, define

`K_irr(D)=sup_(sigma irreducible, dim sigma<=D)`
`  delta_sigma(w)/sum_(r in R)delta_sigma(r)`.               `(IDR11)`

**Theorem 2 (bounded irreducible degree).**  If `w in Rad_sof(P)`, then

`K_irr(D)<infinity for every fixed D`.                       `(IDR12)`

**Proof.**  It suffices to fix one dimension `d<=D`.  On `U(d)^k`, collect
the matrix defects

`Phi(U)=(pi_U(r)-1)_(r in R)`,
`Psi(U)=pi_U(w)-1`.                                          `(IDR13)`

If `Phi(U)=0`, then `pi_U` factors through `P`.  Its image is a finitely
generated complex linear group, hence residually finite and sofic; radical
membership forces `Psi(U)=0`.

Suppose the ratio of the squared norms in `(IDR13)` were unbounded.  By
semialgebraic curve selection there would be a real-analytic arc `U(t)` to
the common zero set such that every relator matrix vanishes to strictly
higher power-series order than the witness matrix.  If `b` is the first
nonzero order of `pi_(U(t))(w)-1`, reduce all generator matrices modulo
`t^(b+1)`.  The relators become exactly one while the witness remains
nontrivial.  This gives a homomorphism

`P -> GL_d(C{t}/(t^(b+1))) -> GL_(d(b+1))(C)`                `(IDR14)`

retaining `w`.  Its finitely generated image is again linear and sofic, a
contradiction.  Thus the dimension-`d` ratio is bounded.  Taking the maximum
over the finitely many `d<=D` proves `(IDR12)`.  End proof.

This is the affine-defect analogue of the jet argument in
`TRUE_FIXED_DIMENSIONAL_ARC_BOUNDARY.md`.

## 4. Arbitrary multiplicity of bounded blocks is harmless

The bounded-degree conclusion is stronger than a bound on total dimension.

**Corollary 3 (subhomogeneous representations).**  For every `D` there is a
finite constant `B_D` such that

`q_pi(w)<=B_D sum_(r in R)q_pi(r)`                           `(IDR15)`

for every finite-dimensional `pi` all of whose irreducible constituents
have dimension at most `D`, regardless of the total dimension or their
multiplicities.

**Proof.**  Write `pi` as a direct sum of irreducible blocks `pi_i` of
dimensions at most `D`.  The conjugate double is a direct sum of the pair
blocks

`pi_i tensor conjugate(pi_j)`,                               `(IDR16)`

each of dimension at most `D^2`.  Decomposing these pair blocks into
irreducibles and applying `(IDR12)` with `D^2`, equations `(IDR6)--(IDR7)`
give `(IDR15)` with `B_D=K_irr(D^2)`.  End proof.

Therefore neither repetition of a fixed block nor increasingly complicated
mixtures of bounded-degree blocks can make the domination ratios diverge.

## 5. The sharpened remaining gate

Combining Theorems 1 and 2 gives

`C_fd<infinity`
` iff sup_(sigma irreducible) delta_sigma(w)/sum_R delta_sigma(r)`
`      <infinity`,                                          `(IDR17)`

and every sequence violating `(IDR17)` can be chosen irreducible with

`dim(sigma_n)->infinity`.                                   `(IDR18)`

On the classical side, the affine defect for a permutation representation
is exactly moved-point proportion.  Orbit decomposition reduces its optimal
constant to transitive permutation representations.  Hence the universal
TRUE problem now compares the two extreme families:

* transitive finite permutation representations;
* irreducible finite-dimensional unitary representations of unbounded
  degree.

The remaining assertion is that a finite domination constant on the first
family forces a finite domination constant on the second.  Direct sums,
multiplicity growth, scalar phases, and every bounded irreducible degree are
now rigorously outside the obstruction.
