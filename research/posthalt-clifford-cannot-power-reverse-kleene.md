---
rg: 2
id: posthalt-clifford-cannot-power-reverse-kleene
kind: claim
title: A post-halt Clifford table cannot supply the threshold-free reverse-Kleene semantics
distinct_from:
  threshold-free-reverse-kleene-fanizza-red-team-audit: that verifies the qualitative reverse-Kleene and Higman package and locates the missing Fanizza groupifier; this tests whether finite Clifford capacity can replace that groupifier and proves that it cannot.
  dimension-reported-clifford-table-halting-compiler: that is the still-valid forward matrix-search route and asks for one precomputed dimension-independent defect modulus; this shows why moving its table activation into a recursively enumerable post-halt relator stream does not remove that quantitative requirement.
  marked-clifford-table-exponential-dimension: that proves the finite same-dimension Gowers--Hatami endpoint; this audits the quantifier change from one reported dimension to all coordinates of a tracial matrix ultraproduct.
---

## Verdict

The tempting splice

```text
threshold-free reverse Kleene
  + enumerate a supercritical E_N table after HALT(D)
  + effective Higman
```

does **not** prove non-hyperlinearity.  There are two independent, exact
obstructions.

1. A reverse-Kleene fixed point halts only after finding a finite proof that
   its mark is trivial.  Relators enumerated after that halt form a further
   quotient and cannot resurrect the mark.  Thus post-halt activation cannot
   establish the HALT-side nontriviality clause `(TFK1)`.
2. A finite Clifford table excludes only matrices below its spin dimension.
   Tracial matrix ultraproducts may use unbounded coordinate dimensions.  Even
   enumerating Clifford tables of every rank with one common sign does not
   kill that sign in the hyperlinear radical or on canonical-profile
   microstates: the resulting infinite extraspecial group is locally finite
   and has an explicit canonical tracial ultraproduct embedding detecting the
   sign.

Consequently Gowers--Hatami exactification closes the **same reported
dimension** endpoint, but it does not supply either `(TFK2)` or `(CPK2)`.  The
direct Clifford route still needs the forward dimension-matched compiler with
a pre-halt modulus, or some genuinely new static group semantics.

## 1. The finite Clifford endpoint has the wrong quantifier

Let `E_N` be the extraspecial Pauli group with common central involution `J`
and `N` Pauli pairs.  The marked Clifford-table theorem says that an all-pairs
`epsilon`-homomorphism

```text
f:E_N -> U(d)
```

with `||f(J)-I||_2>42 epsilon` satisfies

```text
d >= (1-4 epsilon^2) 2^N.                         (LCT1)
```

This is dimension-free in its **constant**, but not in its conclusion.  Once
`N` is fixed, representations in dimensions at least `2^N` are permitted.
Therefore activating `E_N` after a program prints `D`, with `2^N>D`, proves
only

```text
no D-dimensional sufficiently accurate model keeps J separated. (LCT2)
```

Threshold-free reverse Kleene instead needs, in the NONHALT case, either

```text
every homomorphism Gamma -> product_omega U(d_n) kills J       (TFK2)
```

or at least collapse along every canonical-profile microstate sequence
`(CPK2)`.  In either formulation the coordinate dimensions `d_n` are free to
grow.  A single finite `N` does not constrain their tail.

Printing a number `D` from a proof certificate does not repair the mismatch.
That `D` is not the dimension of a hostile canonical microstate.  A fixed
final presentation containing `E_N` still admits marked models in dimensions
`2^N,2^(N+1),...`, and an ultraproduct may use only such dimensions.

## 2. Every-rank activation still has a canonical hyperlinear model

The strongest obvious repair is to enumerate not one table but all of them.
It has an exact countermodel.

Let

```text
E_infty = union_(N>=1) E_N,                            (LCT3)
```

where the inclusions retain the same central sign `J` and add one new Pauli
pair at each step.  Every finitely generated subgroup of `E_infty` is
contained in some finite `2`-group `E_N`.  Hence `E_infty` is locally finite,
amenable, sofic, and hyperlinear.

More explicitly, for `g in E_m` and `n>=m`, let `lambda_n(g)` be the matrix of
left translation by `g` in the regular representation of `E_n`.  The
sequences

```text
g |-> (lambda_n(g))_(n>=m)                            (LCT4)
```

define a homomorphism from `E_infty` to a tracial matrix ultraproduct.  For
every nonidentity `g`,

```text
tr(lambda_n(g))=0                                     (LCT5)
```

for all sufficiently large `n`.  Thus `(LCT4)` realizes the canonical delta
character.  In particular

```text
||lambda_n(J)-I||_2^2=2,                              (LCT6)
```

so the common sign survives maximally.

This example is especially diagnostic because **every exact
finite-dimensional representation of `E_infty` kills `J`**.  Indeed, if
`rho:E_infty->U(d)` had a nonzero `J=-1` sector, restriction to every `E_N`
would make that sector a sum of spin representations and hence would force

```text
d >= 2^N                                              (LCT7)
```

for every `N`, an impossibility.  Thus exact finite-dimensional invisibility
of the mark, even proved by the complete Clifford table at every rank, does
not imply hyperlinear-radical membership or canonical-profile collapse.
The regular representations in `(LCT4)` satisfy each **fixed** finite table
eventually while their dimensions grow with the table rank.

This is the precise quantifier exchange that the proposed shortcut would
need but does not possess:

```text
for every fixed N, eventually the N-table is accurate
```

does not imply

```text
for one coordinate n, every N-table is accurate below dimension d_n.
```

## 3. Post-halt relators cannot establish reverse-Kleene completeness

There is also a purely recursion-theoretic obstruction, independent of
matrix estimates.

Consider the advertised implementation in which the relator enumerator for
machine `e` emits a dormant stream until it observes `e` halt and only then
emits the multiplication table of `E_(N(D))`, tying its sign to the marked
word `w_e`.  The reverse-Kleene program `P_e` dovetails this same stream and
halts when it finds a finite normal-closure certificate

```text
w_e in <<R_e>>.                                       (LCT8)
```

At the recursion fixed point, if `P_(e_*)` halts, the certificate `(LCT8)`
uses relators which were already emitted before the post-halt activation was
available.  That finite certificate remains valid after every later relator
is appended.  Adding relators replaces a group by a quotient, so it cannot
turn a trivial word into a nontrivial one.  Consequently the final activated
presentation still has

```text
w_(e_*)=1.                                            (LCT9)
```

This directly contradicts the HALT semantic clause needed by reverse Kleene,

```text
e_* halts => w_(e_*) != 1.                            (TFK1)
```

The obstruction is not cured by choosing `N>D`, by using the full
multiplication table, or by improving the Gowers--Hatami constants.  Those
steps constrain representations of the quotient; they cannot invalidate the
pre-existing proof `(LCT8)`.

Equivalently, approximation-invisible radicals are monotone under quotients.
If `q:G->Q` is onto and `w` is killed by every homomorphism from `G` to a
tracial matrix ultraproduct, then `q(w)` is killed by every such homomorphism
from `Q`, because every map out of `Q` composes with `q`.  A relator-only
activation cannot turn a genuinely dormant radical mark into the
finite-dimensionally visible sign of `E_N`.

The only way around this timing argument is for HALT-side nontriviality to be
a semantic property of the static compiled presentation, not something
created by relators appended after the proof-search program halts.  Producing
such static semantics is exactly the perfect-completeness compiler problem
that the shortcut was meant to avoid.

## 4. Computability and finite generation do not repair the semantics

There is a minor implementation issue as well.  A total compiler must output
its finite generating alphabet before learning an unbounded halting output
`D`, while the literal table of `E_(N(D))` has an unbounded number of named
generators and elements.  This can in principle be repaired by a fixed
addressing group whose conjugate words name the later table, or by first using
a countable recursive presentation and a suitable embedding construction.
It is not the decisive obstruction.

Even granting perfect effective addressing, Sections 1--3 remain: the table
has only a same-dimension consequence, the all-ranks limit has the canonical
hyperlinear model `(LCT4)`, and post-halt quotienting cannot reverse a
triviality certificate.

## 5. Effective Higman is downstream, not an amplifier

Effective Higman embedding is exactly adequate after one has constructed a
finitely generated recursively presented **non-hyperlinear** group.  If its
finitely presented host were hyperlinear, the embedded subgroup would be
hyperlinear, giving the desired contradiction.

It does not turn a hyperlinear source such as `E_infty` into a known
non-hyperlinear group, and it does not transport `(LCT2)` into unconditional
radical collapse.  No quantitative distortion estimate is needed in the
valid reverse-Kleene proof, but conversely no Higman distortion estimate can
manufacture the missing source-level `(TFK2)` or `(CPK2)` semantics.

## 6. Exact claim boundary

This audit does not invalidate the forward route
`dimension-reported-clifford-table-halting-compiler`.  In that route the
fixed-point program searches for an actual finite-dimensional hostile tuple,
prints its **same** dimension, and uses a compiler modulus fixed before the
search.  Then `(LCT1)` is exactly the correct endpoint.

What fails is the proposed attempt to remove that modulus by moving the table
into a post-halt recursively enumerable stream and switching to proof-search
reverse Kleene.  Proof search supplies no hostile dimension; finite Clifford
capacity supplies no qualitative ultraproduct radical; and late relators
cannot create the HALT-side nontrivial mark.

Thus the remaining alternatives are unchanged:

1. prove a forward dimension-matched Clifford compiler with a positive
   pre-halt defect modulus (or a sufficient amplification envelope); or
2. build a static HALT/NONHALT groupifier satisfying `(TFK1--TFK2)` or the
   weaker canonical-profile clauses `(CPK1--CPK2)` by a mechanism beyond
   finite Clifford dimension growth.
