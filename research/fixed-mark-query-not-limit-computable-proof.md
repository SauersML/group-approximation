---
rg: 2
id: fixed-mark-query-not-limit-computable-proof
kind: route
title: No convergent computable learner recognizes the fixed non-MF query
target: fixed-mark-query-not-limit-computable
requires:
  - fixed-mark-query-enumerated-second-level-complete
---

# The fixed non-MF query is not limit computable

## Operational notion

For a predicate `P` on program codes, a *convergent computable classifier* is
a total computable Boolean function

```text
guess : Code × Nat -> Bool
```

such that for every code `c` there is a stage after which `guess(c,s)` is
constant, and its eventual value is true exactly when `P(c)` holds.  This is
the operational, mind-change definition of limit computability; no hierarchy
theorem or limit lemma is imported.

## Diagonal theorem for infinite domain

Assume that `guess` is a convergent computable classifier for
`InfiniteDomain`.  From a prospective self-code `c` and input `n`, define the
partial computation

```text
D(c,n) searches for s >= n with guess(c,s) = false;
D(c,n) halts with output 0 at the first such s.
```

Because `guess` is total computable, `D` is partial recursive uniformly in
`(c,n)`.  Kleene's second recursion theorem supplies a code `d` satisfying

```text
eval(d,n) = D(d,n).
```

Consequently

```text
n is in domain(d) iff exists s >= n, guess(d,s) = false.
```

There are now two exhaustive cases.

1. Suppose `domain(d)` is infinite.  Correct convergence says that
   `guess(d,s)` is eventually true.  Hence false guesses occur at only
   finitely many stages.  If `B` is beyond all of them, then no `n >= B`
   belongs to `domain(d)`.  The domain is finite, contradiction.

2. Suppose `domain(d)` is not infinite.  Since subsets of `Nat` are either
   finite or infinite, the domain is finite.  Correct convergence says that
   `guess(d,s)` is eventually false.  For every input `n`, choose
   `s >= max(n,N)` beyond the convergence stage.  Then `guess(d,s)=false`, so
   `n` belongs to `domain(d)`.  The domain is all of `Nat`, contradiction.

Therefore `InfiniteDomain` has no convergent computable classifier.  Negating
the eventual Boolean shows the same for `FiniteDomain`.

## Transport to the standard presentation query

The already proved compiler

```text
compile : Code -> PresentationCode
```

is computable and satisfies

```text
KILL(compile(c)) iff InfiniteDomain(c),
SURV(compile(c)) iff FiniteDomain(c),
OperatorMF(compile(c)) iff InfiniteDomain(c),
NonOperatorMF(compile(c)) iff FiniteDomain(c).
```

If any of these four target predicates had a convergent computable classifier,
precomposing its code input with `compile` would give one for
`InfiniteDomain` or `FiniteDomain`.  This contradicts the diagonal theorem.

Thus none of the following can be learned in the limit from a standard
enumerated presentation code:

* whether every marked homomorphism kills the fixed MF-invisible mark;
* whether some marked homomorphism retains it;
* whether the presented group is Operator-MF;
* whether the presented group is non-Operator-MF.

This is stronger than undecidability and stronger than failure of both
positive and negative semidecision.  It rules out every total computable
recognizer that is allowed arbitrarily many early mistakes but must eventually
stabilize to the correct answer.

## Dependency audit

The proof uses only:

1. total computability of the proposed Boolean guesser;
2. unbounded search for a decidable witness;
3. the internally formalized second recursion theorem;
4. elementary finite/infinite reasoning for subsets of `Nat`;
5. the already proved computable switch compiler and its exact four-way truth
   table.

No arithmetical-hierarchy separation theorem, limit lemma, oracle theorem,
finite-presentation compiler, or literature result is used.
