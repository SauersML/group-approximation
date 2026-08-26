---
rg: 2
id: fixed-mark-query-enumerated-presentations-second-level-proof
kind: route
title: Compile the exact ray switch into the standard enumerated-presentation syntax
target: fixed-non-mf-mark-query-enumerated-presentations-is-second-level-complete
requires:
  - exact-literal-e-fin-inf-switch
  - literal-central-mark-corona-invisible
---

# Fixed non-MF marked query on enumerated presentations: second-level proof

## The standard syntax

An enumerated countable presentation is coded by a partial-recursive program
`c`.  Decode an address `a` as a pair `(input, stage)`.  If the step-indexed
evaluator `evaln stage c input` has produced the natural number `z`, decode
`z` as a raw word on generators `ℕ`; if evaluation or decoding has not
succeeded, use the empty word.  Write the resulting total raw-word family as
`r_c(a)` and put

```text
R_c = { freeEval(r_c(a)) | a ∈ ℕ },
P_c = PresentedGroup(R_c).
```

The default empty word adds only the identity relator and therefore changes
no normal closure.  Pairing, `evaln`, decoding and raw-word evaluation are all
effective.  Conversely, every partial-recursive enumeration of raw relators
is represented by this syntax, up to harmless repetitions and the identity
relator.

## Uniform word-problem certificates

Membership of a free word `v` in the symmetrization of `R_c` has a finite
certificate:

1. an enumeration address `a`;
2. a sign choosing `r_c(a)` or its inverse;
3. a free-reduction certificate showing that the chosen raw word and `v`
   represent the same free-group element.

The certificate matrix is primitive recursive.  A word is trivial in `P_c`
iff it is a finite product of conjugates of symmetrized relators.  Thus a word
problem certificate consists of finitely many conjugators and certified
relators, followed by one free-reduction certificate.  Its matrix is again
primitive recursive, uniformly in `c`.

Consequently the word problem of every `P_c` is recursively enumerable
uniformly in its presentation code.  This conclusion is derived from the raw
normal-closure certificate; it is not an assumed recursive-presentation
interface.

## The fixed marked query

Fix the already proved eight-generator, forty-one-relator non-MF group `E`
and its nontrivial MF-invisible mark `w`.  Define

```text
SURV(c) := ∃ φ : E → P_c, φ(w) ≠ 1,
KILL(c) := ∀ φ : E → P_c, φ(w) = 1.
```

A `SURV` witness is:

1. eight target raw words;
2. one word-problem certificate for each of the forty-one substituted source
   relators;
3. the assertion that no word-problem certificate kills the substituted
   mark.

After coding the finite tuple into one natural, this has the form `∃x ∀y` with
a computable Boolean matrix.  Hence `SURV` is `Σ⁰₂` and `KILL`, its complement,
is `Π⁰₂`.  The usual universal property of `PresentedGroup` proves that the
certificate predicate is exactly the displayed homomorphism predicate.

If `SURV(c)`, functoriality carries MF-invisibility of `w` to the nontrivial
element `φ(w)`.  Therefore `P_c` is non-MF.

## The computable switch compiler

For a partial-recursive program code `e`, use the previously proved
first-halting dovetail stream.  Enumerate the exact ray-switch relators by a
total computable raw-word family:

1. decode an index as `(stage, slot)`;
2. slots `0,...,40` emit the forty-one source relators in the copy at that
   stage;
3. slots `41,...,48` emit, for the corresponding source generator, the bridge
   relation to the next stage when the event bit is false and the killing
   relation when it is true.

Number the copy generator `(stage,g)` by

```text
8 * stage + generatorIndex(g).
```

This is an explicit computable bijection `ℕ × Fin 8 ≃ ℕ`.  The raw switch
family is primitive recursive uniformly in `e`.  A universal program followed
by `Code.curry` therefore gives a computable presentation-code compiler
`compile(e)` whose enumerated relator set is the relabelled switch set, plus
only the harmless identity relator.

Relabelling along the displayed bijection gives an explicit isomorphism

```text
P_compile(e) ≃ SwitchTarget(e).
```

It carries the canonical tail-copy homomorphism and the fixed mark exactly.

## Completeness

The exact switch theorem gives

```text
KILL(compile(e)) iff InfiniteDomain(e),
SURV(compile(e)) iff FiniteDomain(e).
```

The compiler is computable.  Since `InfiniteDomain` is `Π⁰₂`-complete and
`FiniteDomain` is `Σ⁰₂`-complete by the internal finite-prefix construction,
`KILL` is `Π⁰₂`-complete and `SURV` is `Σ⁰₂`-complete on the standard
enumerated-presentation syntax.

No finite-presentation compiler, Higman embedding theorem, Chiodo theorem,
external index-set theorem, or literature assumption occurs in this proof.

## Further strict consequences

Two direct halting reductions strengthen mere undecidability.

* A code whose domain is infinite exactly after a chosen computation halts
  reduces the non-r.e. nonhalting side to `SURV`.
* A code whose domain grows for precisely as long as the chosen computation
  has not halted reduces nonhalting to `KILL`.

Thus neither `SURV` nor `KILL` is recursively enumerable.  Since they are
complements, neither is co-r.e. either.  In particular there is no algorithm,
positive semidecision procedure, negative semidecision procedure, or complete
finite certificate system for either side of the fixed marked query.
