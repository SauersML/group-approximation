---
rg: 2
id: sofic-promise-mf-recognition-two-isomorphism-types-proof
kind: route
title: MF recognition stays second-level complete on a two-valued sofic family
target: sofic-promise-mf-recognition-two-isomorphism-types
requires:
  - fixed-mark-query-enumerated-second-level-complete
  - literal-sofic-assembly
---

# MF recognition is Pi-zero-two complete under a sofic promise

## Statement

There is a computable map from partial-recursive program codes to standard
enumerated group-presentation codes,

```text
compile : Code -> PresentationCode,
```

such that every presented group `G_c = Carrier(compile(c))` is sofic and in
fact has one of only two isomorphism types:

```text
InfiniteDomain(c)  =>  G_c is trivial,
FiniteDomain(c)    =>  G_c is isomorphic to E.
```

Here `E` is the one fixed eight-generator, forty-one-relator group already
proved sofic and non-Operator-MF.  Consequently

```text
G_c is Operator-MF      iff InfiniteDomain(c),
G_c is non-Operator-MF  iff FiniteDomain(c).
```

Thus actual Operator-MF recognition on this computable family of sofic groups
is `Pi^0_2`-complete, and actual non-Operator-MF recognition is
`Sigma^0_2`-complete.  Equivalently, global recognition is hard at those
levels even when every instance produced by the reduction satisfies the sofic
promise.

## Why every target is sofic

The event-ray switch already has an exact semantic dichotomy.

* If events are unbounded, every named stage generator is killed, so the
  switch group is subsingleton.  A subsingleton group is finite and hence
  sofic.
* If events have a last cut, the explicit `collapseHom` and `stageHom` are
  inverse group homomorphisms between the switch group and `E`.  The theorem
  `LiteralSoficAssembly.markedGroup_isSofic` proves `E` sofic without a
  hypothesis or literature input, so soficity transports across this
  equivalence.

For every code, `InfiniteDomain` or `FiniteDomain` holds by the ordinary
finite/infinite dichotomy for subsets of `Nat`.  Hence the switch group is
sofic in all cases.  The end-to-end equivalence

```text
standardCarrierEquivSwitch(c) :
  Carrier(compile(c)) ~= SwitchTarget(c)
```

transports soficity to the standard compiled presentation.

## MF truth table

The infinite-domain branch is a finite trivial group, hence Operator-MF.  In
the finite-domain branch the target is isomorphic to `E`, whose fixed
MF-invisible mark is nontrivial, so it is not Operator-MF.  This is already
formalized as

```text
compiled_operatorMF_iff_infiniteDomain,
compiled_nonOperatorMF_iff_finiteDomain.
```

Define the restricted predicates on source program codes by

```text
SoficSwitchMF(c)    := OperatorMF(Carrier(compile(c))),
SoficSwitchNonMF(c) := not SoficSwitchMF(c).
```

The displayed truth table identifies them pointwise with `InfiniteDomain`
and `FiniteDomain`.  The internally proved completeness of those two index
sets therefore gives

```text
Pi02Complete SoficSwitchMF,
Sigma02Complete SoficSwitchNonMF.
```

No global upper bound for arbitrary recursively presented groups is needed:
membership at the second level follows directly from the exact equivalence on
this restricted family.

## Promise-hardness formulation

For predicates `P` and `Q` and a promise `S` on target codes, say that `P`
many-one reduces to `Q` under `S` when there is a computable map `f` such that

```text
forall x, S(f(x)),
forall x, P(x) iff Q(f(x)).
```

The same compiler witnesses:

```text
Pi02HardUnder SoficCode OperatorMFCode,
Sigma02HardUnder SoficCode NonOperatorMFCode.
```

This formulation makes clear that the reduction never leaves the sofic
promise, while the restricted-family completeness theorem supplies the exact
upper classification.

## Strength of the restriction

This is stronger than merely promising soficity.  The constructed inputs vary
only in their recursive presentations; semantically every group is either
`1` or the same fixed group `E`.  Therefore the second-level hardness cannot
be attributed to a growing zoo of group structures, generators, answer
alphabets, or approximation classes.  It is the problem of determining which
of two fixed sofic isomorphism types a program-generated presentation denotes.

## Dependency audit

The proof uses only:

1. the primitive-recursive event stream and standard presentation compiler;
2. the explicit infinite-event collapse and finite-cut equivalence;
3. the premise-free Lean theorem that `E` is sofic;
4. finite groups are sofic and soficity is invariant under group equivalence;
5. the internally proved `INF`/`FIN` second-level completeness theorems.

No Higman embedding, Mikaelian or Chiodo compiler, nonlocal-game theorem,
sofic quotient permanence, hierarchy-separation theorem, or other literature
input occurs.
