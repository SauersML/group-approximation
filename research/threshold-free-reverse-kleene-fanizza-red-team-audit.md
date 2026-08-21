---
rg: 2
id: threshold-free-reverse-kleene-fanizza-red-team-audit
kind: claim
title: Threshold-free reverse Kleene is sound, but Fanizza supplies only the BCS analogue of TFK2
---

## Verdict

The package

```text
threshold-free-reverse-kleene-higman-diagonal
hyperlinear-radical-presentation-compactness
effective Higman embedding
```

has no hidden numerical-effectivity or presentation gap under its stated
hypotheses.  It really does reduce the existence of a finitely presented
non-hyperlinear group to the two semantic clauses

```text
e halts      => w_e != 1 in Gamma_e,                  (TFK1)
e nonhalts   => w_e in Rad_hyp(Gamma_e).              (TFK2)
```

for a **total computable**, uniformly recursively presented, finitely
generated group family.  No finite-matrix cutoff or computable convergence
modulus is needed.

The Fanizza native signal has exactly the correct HALT/NONHALT orientation,
but the published BCS theorem does not itself supply `(TFK2)`.  It supplies
the analogous statement only for representations which already carry the
additive projection/context structure of a BCS strategy.  Promoting that
statement to every homomorphism of an ordinary group into a tracial matrix
ultraproduct is precisely the remaining groupification theorem.

## 1. Computability and presentation audit

Assume the compiler uniformly computes a finite alphabet `S_e`, a word
`w_e`, and an enumerator for `R_e`.  The fixed-point program can dovetail the
relator enumerator with all finite expressions

```text
w_e = product_j a_j r_(i_j)^(+-1) a_j^(-1).
```

Every certificate uses only finitely many relators, so if `w_e=1` in
`<S_e|R_e>`, one certificate is eventually found.  Conversely every found
certificate proves triviality.  Thus the proof search is a genuine partial
computable procedure even though no word-problem decider and no soundness
modulus is available.

Kleene's recursion theorem applies because the compiler is total and the
presentation stream is uniform in `e`.  If its fixed-point program halted,
the found certificate would contradict `(TFK1)`.  It therefore does not
halt; completeness of the certificate enumeration then also gives
`w_(e_*)!=1`.  Clause `(TFK2)` makes this nontrivial word invisible in every
tracial matrix ultraproduct, so `Gamma_(e_*)` cannot itself embed in such an
ultraproduct and is non-hyperlinear.

Classical Higman embedding is used only after this qualitative
non-hyperlinearity conclusion.  A finitely generated recursively presented
group embeds effectively in a finitely presented group.  If the host were
hyperlinear then its subgroup `Gamma_(e_*)` would be hyperlinear.  Hence no
quantitative defect transport, marked-word radical preservation in the host,
or relative Dehn bound is required.  Mikaelian's explicit algorithm
(`arXiv:2507.04347`) provides the advertised effective form for effectively
enumerable generators and recursively enumerable relations.

## 2. Compactness audit

For a finite or recursively enumerable presentation, the equivalence

```text
w in Rad_hyp(Gamma)
<=>
for every epsilon>0, some finite relator window and some delta>0
force ||w(U)-I||_2<epsilon
```

is valid and non-effective.  Negating the right side yields a sequence whose
first `n` relators have defect below `1/n` while the mark stays separated; a
metric ultraproduct gives a homomorphism detecting `w`.  Conversely,
representatives of any ultraproduct homomorphism satisfy every fixed finite
window asymptotically.  The fixed-point program never needs to find the
window or `delta`.

There is likewise no tensor-power loophole.  An unconditioned group-level
cutoff below `sqrt(2)` kills the mark in every exact finite-dimensional
representation and in every tracial matrix-ultraproduct homomorphism.  The
argument applies each fixed tensor power coordinatewise.  This firewall does
not apply to trace-conditioned cutoffs, because the auxiliary trace tests
need not survive tensor powers; the threshold-free package correctly asks
for unconditional radical membership instead.

## 3. What Fanizza supplies before groupification

For `L=HALT`, Fanizza--Kroell--Mehta--Paddock--Rochette--Slofstra--Zhao
(`arXiv:2510.04943`) computably produce finite BCS systems `B_m` and the native
involution `d_m=x_(D,m)`, with `D_m=(1-d_m)/2`, such that

```text
m halts
  => a tracial BCS GNS representation has d_m != I;

m nonhalts
  => every epsilon-perfect BCS strategy satisfies
     phi(D_m) <= C_m epsilon.
```

The HALT clause is already the pre-groupification form of `(TFK1)`: any exact
group extension of that one GNS representation certifies that the retained
word is algebraically nontrivial.  No tracial extension of the auxiliary
groupifier is required.

The NONHALT clause gives only

```text
epsilon_n-perfect BCS strategies, epsilon_n -> 0
  => ||X_(D,m)-I||_2 -> 0.                             (BCS-TFK2)
```

Actual `(TFK2)` instead quantifies over **every** homomorphism

```text
theta: Gamma_m -> product_omega U(d_n).
```

Such a homomorphism initially remembers multiplication of group words only.
It need not preserve sums of spectral projections, forbidden-assignment
idempotents, or the consistency data needed to be a BCS strategy.  Therefore
`(BCS-TFK2)` implies `(TFK2)` only after proving one of the following
equivalent-strength groupifier semantics:

1. every such `theta` decodes to asymptotically perfect finite-dimensional
   BCS strategies and identifies `theta(d_m)` with their Bob signal; or
2. directly, every such `theta` kills `d_m`, by a matrix-only argument which
   need not construct coordinate strategies.

No effective coordinate modulus is required in either version.  But the
universal quantifier over group ultraproduct homomorphisms is essential and
is not present in the Fanizza source theorem.

## 4. Exact counterexample to the naive multiplicative-shadow compiler

Even enumerating **all group-word identities valid in a nonlinear BCS
algebra** does not repair this categorical gap.

Let

```text
R={(+1,+1),(+1,-1),(-1,+1)}
```

and let `A=C^R`.  Let `x,y in U(A)` be the two coordinate-sign functions.
This is the commutative BCS context which forbids only the assignment
`(-1,-1)`; algebraically its nonlinear support relation is

```text
(1-x)(1-y)=0.                                         (4.1)
```

The multiplicative subgroup generated by `x,y` is nevertheless exactly
`C_2 x C_2`.  Indeed the four functions `1,x,y,xy` are distinct on `R`, so
the natural map `C_2 x C_2 -> U(A)` is injective.  Consequently the full list
of multiplicative word identities holding for `x,y` consists only of the
ordinary `C_2 x C_2` identities.

There is an exact one-dimensional representation of this multiplicative
shadow with

```text
x |-> -1,
y |-> -1.
```

It is a finite-dimensional, hence matrix-ultraproduct, group representation,
but it cannot extend to a star-homomorphism `A->C`: evaluating `(4.1)` would
give `4=0`.  Thus the forbidden nonlinear atom reappears in an exact group
representation even after every valid group-word consequence has been
imposed.

This does not rule out a groupifier with additional infinite actuators,
finite packet multiplicity, Toeplitz return, or another matrix-only
mechanism.  It does rule out the tempting shortcut

```text
take the group generated by the BCS involutions and enumerate all
multiplicative identities inherited from the BCS algebra.
```

That shortcut cannot turn Fanizza soundness into `(TFK2)` for nonlinear
contexts.

## 5. Exact remaining compiler interface

The threshold-free route has therefore isolated the following minimal open
object.

Totally computably from `m`, construct a finite generating set, a uniformly
r.e. ordinary group presentation `Gamma_m`, and a word `d_m` such that:

```text
FTFK1.  If m halts, one exact (possibly properly infinite and nontracial)
        representation of Gamma_m sends d_m away from I.

FTFK2.  If m nonhalts, every homomorphism from Gamma_m to every tracial
        matrix ultraproduct sends d_m to I.
```

Fanizza proves the BCS source statements needed on both sides.  The HALT
extension and the NONHALT additive-to-multiplicative ultraproduct transfer
remain groupifier obligations.  Of these, only the latter is the analytic
soundness barrier; countable amplification/proper infiniteness may be used
freely for the former.

## Claim boundary

This audit establishes the reverse-Kleene, compactness, and Higman logic and
gives a finite exact counterexample to a naive multiplicative-shadow
groupification.  It does **not** prove that no ordinary-group compiler can
realize `FTFK1--FTFK2`, and it does not prove a non-hyperlinear group.  The
open node `fanizza-native-signal-ultraproduct-groupification` is exactly the
remaining semantic bridge, now without any unnecessary demand for a
computable Hilbert--Schmidt modulus.
