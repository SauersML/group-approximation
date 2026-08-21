# Adversarial error delocalization: second-pass breakthrough designs

**Date:** 2026-08-21

## Outcome

This note turns the latest self-aware-machine, heavy-tail, recursive-copying,
and closed-loop-verification ideas into three precise construction targets.
It does **not** claim an unconditional non-hyperlinear group.  Its purpose is
to distinguish mechanisms that survive normalized-HS dilution from versions
already ruled out by direct sums, amplification, or an infinite safe tail.

The central rule is:

```text
late failure is useful only if a fixed finite interface returns it to
a positive-density carrier with a dimension- and runtime-independent cost.
```

This is stronger than finding a failure at every finite dimension.  A profile
whose required dimension merely tends to infinity is compatible with
hyperlinearity.

## 1. Heavy tails must live on addresses, not operator magnitude

A literal Cauchy-tail construction is pointed in the wrong direction.  Group
words evaluated on unitaries are uniformly bounded, while an unbounded
functional such as a logarithmic determinant can be changed by an arbitrarily
small reducing corner.  The established nodes
`word-recursion-cannot-amplify-sublinear-summands` and
`bounded-hs-loss-kills-static-heavy-tail-library` give the two relevant
firewalls.

The useful analogue of a heavy tail is instead a distribution on **challenge
addresses**.  Let a finitely generated actor `H` move a challenge space
`Omega`, and let a constant-size predicate packet test one orbit edge at a
time.  The desired estimate is

```text
sum_(s in S) sum_(omega in Omega)
  ||P_(s omega) U_s - U_s P_omega||_2^2
  <= C Def_R(U)^2,                                      (A1)
```

where the `P_omega` form one common spectral PVM and `C` is independent of the
finite model and of how far out in `Omega` the active challenge lies.  An
infinite Schreier gap then prevents a defect from escaping to a nonstandard
address.  This is the exact content sought by
`infinite-character-actor-word-energy-interface`; the new interpretation is
that `(A1)`, rather than an unbounded matrix statistic, is the correct
heavy-tail analogue.

Fast falsification test: if the proposed address sampler is amenable or the
PVMs depend on the address separately, Folner compressions or incoherent
multiplicity gauges give canonical microstates with boundary loss tending to
zero.  A proposal must exhibit one common PVM and a nonamenable summed-energy
identity before any machine semantics matter.

## 2. Streaming Gram overflow

There is a dimension detector more geometric than evaluating the growing
Amitsur--Levitzki polynomial.  For a separated word `w` and conjugating words
`h_i`, consider centered operator vectors

```text
v_i = U(h_i w h_i^(-1))
      - tr(U(h_i w h_i^(-1))) I                         (G1)
```

in `L^2_0(M_d)`, a space of dimension `d^2-1`.  In the regular
representation, distinct conjugates are orthogonal whenever the corresponding
group elements are distinct.  In a `d`-dimensional matrix model, no family of
more than `d^2-1` vectors can have identity Gram matrix.

Naming `d^2` conjugates is useless: the presentation is fixed, and every fixed
prefix fits once `d` is large.  The possible breakthrough is a **streaming
Gram verifier** with these clauses.

1. A finite controller addresses conjugates by words and incrementally checks
   one new Schur complement or QR pivot.
2. A finite multiplicity oracle detects the first index at which the current
   operator-space Gram rank is exhausted.
3. Failure of that pivot activates a fixed finite flag.
4. A constant-gap PCP/expander return carries the flag back to the separated
   marked carrier with loss at most `C Def_R(U)`, where `C` is independent of
   `d`, the pivot index, and runtime.
5. Corrupting the address, inner-product, or pivot computation itself pays a
   fixed fraction of normalized-HS energy on the same carrier.

If all five clauses are realized by group words, the contradiction occurs
inside the candidate model:

```text
rank Gram(v_1,...,v_N) <= d^2-1 < N,
```

while sound verification asserts that every tested pivot is bounded below.
This is a same-model `d >= F(d) > d` mechanism, but it replaces an all-pairs
Clifford table by a streaming rank certificate.

Fast falsification tests:

- Direct evaluation of a Gram determinant has degree and coefficient mass
  growing with `N`; that merely recreates the Amitsur--Levitzki loss.
- Ordinary Gram--Schmidt is ill-conditioned near a small pivot.  The verifier
  needs a constant promised gap (for example a block-pivot or rank-testing
  game), not division by the pivot.
- A verifier that checks only the encountered path can be corrupted on a
  vanishing set of addresses.  Constant-degree expansion and a shared marked
  carrier are mandatory.
- Producing a larger challenge only in a later matrix model proves a growing
  hyperlinear profile, not non-hyperlinearity.

This route is adjacent to, but not identical with,
`same-model-supercritical-clifford-trigger`: Clifford capacity uses many
pairwise anticommuting observables and an exponential divisibility bound;
streaming Gram overflow uses linear dependence in the adjoint operator space
and may admit a smaller local verifier.

## 3. Finite cyclic self-verification: what it can and cannot do

A finite cycle of mutually checking components is useful only after a
positive-density carrier has been authenticated.  A closed verification loop
does not by itself defeat dilution: on a block diagonal tuple every component
and every verifier word preserves the bad reducing projection, so the entire
loop may be copied onto an `o(d)` block.

The viable finite-loop statement has the form

```text
tau(p) >= beta,
||E_N(p)||_2^2 <= (1-gamma) tau(p),
sum_(s in S)||[s,p]||_2^2 <= C Def_R(U)^2.              (V1)
```

The first line authenticates macroscopic mass; the second prevents the full
packet commutant from absorbing the carrier; the third charges every route
around the verification cycle to defining relators.  The established
`relative-fixed-algebra-payment-lemma` then gives the fixed contradiction
`Def_R(U)^2 >= kappa gamma beta/C`.

Thus the right closed-loop engineering question is not “who verifies the
verifier?” It is “which finite holonomy makes the carrier fail the full
fixed-algebra test?” This points toward signed packet holonomy, projective
commutant transfer, and balanced-product syndrome expansion.

## 4. Signed-corner trace promotion remains the cleanest bypass

Let `B` be the fixed finite BCS algebra with tracial states but no
Connes-embeddable tracial state.  If one constructs a group `Gamma`, a finite
subgroup type projection `q`, and a unital algebraic map

```text
B -> q C[Gamma] q,                                      (H1)
```

then the canonical trace on the positive corner pulls back to a forbidden
trace on `B`.  The established theorem
`nonce-bcs-unital-algebraic-corner-map-forces-nonhyperlinear` immediately
makes `Gamma` non-hyperlinear.  This route completely avoids approximate
machine execution.

The local finite-dimensional packet problem and rational rank balancing are
already solved.  The narrow obstruction is a non-tree incidence chord: the
context matrix blocks must escape the finite root algebra while their signed
shared marginals remain literally equal.  Graphs of finite groups cannot do
this—those groups are virtually free/hyperlinear, so such a construction
would contradict the no-CE property.  The chord must therefore use a genuinely
infinite algebraic corner or a nonamenable relative-position mechanism.

A useful synthesis with the closed-loop idea is to seek one finite signed
holonomy cycle whose product is invisible on every shared marginal but acts
nontrivially on the external multiplicity algebra.  This is exactly where
“different elements force incompatible errors in different places” becomes
an algebraic, canonical-trace statement rather than an approximate runtime
statement.

## 5. Priority order

1. Try the signed-corner chord first: it bypasses every quantitative HS and
   runtime issue if the algebraic corner map can be built.
2. In parallel, formulate a constant-gap streaming rank test that avoids
   determinant/Gram--Schmidt conditioning.  Reject the route immediately if
   the soundness coefficient grows with the pivot index.
3. Treat the infinite-character interface as the mathematically correct
   heavy-tail route.  Demand a common-PVM Parseval identity before developing
   actor or machine syntax.
4. Use finite cyclic verification only as the final return mechanism on an
   already positive-density, no-capture carrier.

No item above is yet the missing unconditional proof.  Each is stated so that
one failed quantitative or algebraic clause can be recorded without blurring
the goal.
