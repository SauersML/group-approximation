# Hyperlinear versus sofic is exactly finiteness of two domination constants

Date: 2026-08-11

## Purpose

`TRUE_LINEAR_SOFIC_RADICAL_INEQUALITY.md` characterizes the sofic radical of
a finite presentation by one linear inequality over finite actions.  The
same amplification argument works for finite-dimensional unitary characters
after conjugate doubling.  It characterizes the hyperlinear radical.

The two optimal constants therefore give a scalar numerical form of the
whole open problem:

> every hyperlinear group is sofic if and only if finiteness of the
> permutation domination constant always forces finiteness of the
> finite-dimensional unitary domination constant.

This is an equivalence, not a solution of the comparison.  Its advantage is
that both sides now use the same finite presentation, the same one witness,
the same relators, and the same nonlinear amplification law.

## Character displacement

Let `F` be a finitely generated free group, let `R subset F` be finite, put

`P=F/normal_closure_F(R)`,                              `(RDC1)`

and fix `w in F`.  If `chi` is a normalized character of a
finite-dimensional unitary representation of `F`, define

`q_chi(g)=1-|chi(g)|^2 in [0,1]`,
`Q_R(chi)=sum_(r in R)q_chi(r)`.                       `(RDC2)`

The conjugate-double representation has normalized character

`psi(g)=|chi(g)|^2`.                                  `(RDC3)`

Hence

`||((pi tensor conjugate(pi))(g)-1)||_2^2=2q_chi(g)`. `(RDC4)`

Under an `m`-fold tensor power,

`q_(chi^m)(g)=1-(1-q_chi(g))^m`.                      `(RDC5)`

This is exactly the Cartesian-power formula for moved-point fractions.

## Qualitative hyperlinear-radical criterion

**Lemma 1.**  The image of `w` belongs to `Rad_hyp(P)` if and only if every
sequence of normalized finite-dimensional characters `(chi_n)` of `F`
satisfies

`Q_R(chi_n)->0  ==>  q_(chi_n)(w)->0`.                 `(RDC6)`

**Proof.**  If `(RDC6)` fails, pass to a subsequence on which
`q_(chi_n)(w)>=eta>0`.  Apply conjugate doubling.  By `(RDC4)`, every
relator tends to the identity in normalized Hilbert--Schmidt norm, while
`w` stays a fixed positive distance from the identity.  The metric
ultraproduct homomorphism therefore factors through `P` and has hyperlinear
image, but does not kill `w`.  Thus `w` is not in `Rad_hyp(P)`.

Conversely, suppose a homomorphism from `P` to a hyperlinear group has
nonidentity value on `w`.  Restrict to its countable image and use the
regular-character formulation of hyperlinearity: there are matrix
microstates whose normalized characters tend to one at the identity and to
zero at every fixed nonidentity element.  Lift the chosen free generators
to their matrices.  They define exact representations of the free group
`F`; the relators have `q`-defect tending to zero, while `q(w)` tends to
one.  This violates `(RDC6)`.  End proof.

The use of `|chi|^2` is essential.  It removes scalar phases on relators and
makes the amplification law `(RDC5)` positive and multiplicative.

## Tensor powers force a linear unitary modulus

**Theorem 2 (linear hyperlinear-radical inequality).**  The following are
equivalent.

1. The image of `w` lies in `Rad_hyp(P)`.
2. There exists a finite constant `C_fd>=0` such that every normalized
   finite-dimensional character `chi` of `F` satisfies

   `q_chi(w)<=C_fd Q_R(chi)`.                          `(RDC7)`

**Proof.**  The linear inequality immediately implies `(RDC6)`.  Conversely,
suppose no finite constant works.  Choose characters `chi_n` and write

`a_n=Q_R(chi_n)`, `b_n=q_(chi_n)(w)>n a_n`.            `(RDC8)`

Lemma 1 gives `b_n->0`.  Set `m_n=ceil(1/b_n)` and replace `chi_n` by the
character of its `m_n`-fold tensor power.  Equations `(RDC5)` and
`1-(1-a)^m<=ma` give total relator defect at most

`m_n a_n<=a_n/b_n+a_n->0`,                            `(RDC9)`

whereas the witness defect is at least

`1-(1-b_n)^(1/b_n)>=1-e^(-1)`.                        `(RDC10)`

This contradicts Lemma 1.  End proof.

Thus the optimal finite-dimensional domination constant is

`C_fd(P,w;R)`
` =sup_(chi:Q_R(chi)>0) q_chi(w)/Q_R(chi)`,            `(RDC11)`

with value `+infinity` allowed, and

`C_fd(P,w;R)<infinity iff w in Rad_hyp(P)`.            `(RDC12)`

## The permutation constant in the same normalization

For a finite action character `theta`, let

`q_theta(g)=1-theta(g)^2`.                             `(RDC13)`

Since `0<=theta(g)<=1`, its ordinary moved-point fraction
`d_theta(g)=1-theta(g)` satisfies

`d_theta(g)<=q_theta(g)<=2d_theta(g)`.                 `(RDC14)`

Therefore Theorem 2 of
`TRUE_LINEAR_SOFIC_RADICAL_INEQUALITY.md` is unchanged if every `d` is
replaced by `q`.  Define

`C_perm(P,w;R)`
` =sup_(theta:Q_R(theta)>0) q_theta(w)/Q_R(theta)`,     `(RDC15)`

where `theta` ranges over nonempty finite action characters.  Orbit
decomposition, together with `(RDC14)`, shows that finiteness may still be
tested on transitive coset actions.  Consequently

`C_perm(P,w;R)<infinity iff w in Rad_sof(P)`.          `(RDC16)`

Every finite action character is a normalized finite-dimensional unitary
character.  Hence

`C_perm(P,w;R)<=C_fd(P,w;R)`.                         `(RDC17)`

This numerical inequality is the familiar inclusion
`Rad_hyp(P) subset Rad_sof(P)`.

## Exact equivalence with the open problem

**Theorem 3 (domination-constant formulation).**  The following are
equivalent.

1. Every countable hyperlinear group is sofic.
2. `Rad_hyp(P)=Rad_sof(P)` for every finitely presented group `P`.
3. For every finite presentation `(RDC1)` and every word `w`,

   `C_perm(P,w;R)<infinity`
`  ==> C_fd(P,w;R)<infinity`.                          `(RDC18)`

**Proof.**  The equivalence `1<=>2` is the finite-presentation localization
proved in `(FPR1)--(FPR12)` of `NOTEPAD.md`.  Equations `(RDC12)` and
`(RDC16)` identify assertion 2 word by word with assertion 3.  End proof.

If the implication fails, the gap is extreme.  There are characters
`chi_n` with

`Q_R(chi_n)->0`, `q_(chi_n)(w)->1`,                   `(RDC19)`

so `C_fd=+infinity`, while `C_perm` is finite.  Conversely any such pair of
constants produces a homomorphism from `P` to a hyperlinear group retaining
the sofic-radical word `w`, and hence a hyperlinear nonsofic image.

## What remains

The universal TRUE theorem has now been reduced to the cross-category
inequality `(RDC18)`.  It would suffice to prove any bound

`C_fd(P,w;R)<=Phi(P,w,R,C_perm(P,w;R))`                `(RDC20)`

with finite right-hand side; no dimension-uniform numerical formula is
required beyond the fixed presentation and word.

Ordinary matrix stability is sufficient but stronger than `(RDC20)`: it
would correct every approximate representation, whereas `(RDC20)` only
forces one word to collapse.  Conversely, generic inequalities for
nonnegative characters are insufficient, because finite action characters
form a strictly smaller cone.  The missing argument must use simultaneously
the normal `0/1` limiting law and the fact that the **same word inequality**
is valid in every finite quasiregular representation.
