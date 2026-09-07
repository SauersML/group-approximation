---
rg: 2
id: leavitt-unit-group-nonsurjunctive
kind: claim
title: The binary Leavitt unit group is not surjunctive
root: true
distinct_from:
  openai-leavitt-unit-nonsofic: that is the nonsoficity of the same group; nonsurjunctivity implies nonsoficity, but nonsoficity supplies no converse implication
  leavitt-unit-group-algebra-not-directly-finite: that is the Kaplansky question for the same group's modular group algebra, a statement about elements of a ring; this is a statement about cellular automata on a full shift, and while the first implies the second the converse is not available
  kl-violating-equation-over-leavitt-unit-group: that asks for a Kervaire--Laudenbach violation over the same group, which would refute its hyperlinearity; this asks for an injective non-surjective cellular automaton, which would refute Gottschalk's conjecture
artifacts:
  - research/artifacts/gottschalk-leavitt-audit-2026-08-17.md
---

Exhibit a finite alphabet `A` and a cellular automaton
`tau : A^G -> A^G` over `G = L_(F_2)(1,2)^x`, the binary Leavitt unit group,
that is **injective and not surjective**.

Since Gottschalk's conjecture asserts that every group is surjunctive, such a
`tau` would refute it.

*Marked `root` because it heads a lane of its own, exactly as
`leavitt-unit-group-algebra-not-directly-finite` does: it is a top-level
external question, not a step toward `q3-4-resolved`, and no route should be
built from it toward that goal.  It is recorded because this repository's
object is the only concrete candidate the question currently has, and because
the graph should say where the Leavitt code does and does not reach.*

## Why this group and not another

Sofic groups are surjunctive (Gromov--Weiss), so any candidate must be
nonsofic, and `G` is the one group for which nonsoficity has been announced
(`openai-leavitt-unit-nonsofic`).  That is the **whole** of the connection.
Non-surjunctivity implies nonsoficity; the converse is not established. Every
statement in the routes below is unconditional — none uses the announcement,
and all would read the same if `G` turned out to be sofic.

## Relation to the Kaplansky lane

This claim sits strictly downstream of
`leavitt-unit-group-algebra-not-directly-finite`: a one-sided inverse in
`F_2[G]` yields the automaton
(`stable-finiteness-failure-refutes-surjunctivity`), so everything in that
lane — the corner construction, the lifting problems, the support-thirteen
floor — is evidence about this question too.  Nothing runs back the other way.

## The one honest warning

The repository supplies a strict self-embedding of a **proper** invariant
subshift (`leavitt-kernel-annihilator-strict-self-embedding`).  That is not a
step toward this claim: the same construction runs over a finitely generated
free group, which is surjunctive
(`subshift-self-embedding-carries-no-surjunctivity-content`).  It is the
dynamical twin of `direct-finiteness-not-inherited-by-quotients`, and both
kill the same shortcut.

## Attempts: a computer that preserves its malformed certificates

The user's proposed totalization uses certificate and syndrome tracks to
avoid losing malformed computational histories. A precise subclass is
now excluded by `certificate-controlled-routing-is-surjunctive`: keep the
certificate, and locally route each output datum from one input datum.
This class is surjunctive over every group, including with multiple data
tracks and finitely many intervening reversible computation stages.

The reason is exact Bernoulli balance of incoming and outgoing reads.
Duplicating an input on a valid certificate forces an unread input on
another certificate, which destroys full-shift injectivity. The excluded
class includes arbitrary complexity of the local routing decision; a
self-aware program does not change this balance.

A further computational construction must therefore explain a mechanism
outside this finite factorization, such as a rule combining several input
values whose global injectivity is not inherited stage by stage. This is
a remaining design requirement, not a constructed counterexample or a
proof that every computational route is impossible.

There is now a precise translation for one larger construction class.
`certificate-linear-counterexamples-compile-to-lamp-algebras` allows
arbitrary local certificate predicates to choose linear combinations of
data. If such a rule is injective and nonsurjective on the full shift,
`certificate-linear-automata-have-local-linear-decoders` supplies a local
linear decoder, and finite Fourier identities turn the pair into
`B A=I`, `A B!=I` over a prime-field group algebra of a regular finite-lamp
wreath product over G. For characteristic two, cubic lamps suffice and
the data matrix size doubles. This would reach Gottschalk on G and the
finite-field algebraic obstruction on the larger group; it is not a proof
of the Kaplansky claim for G itself.

The remaining construction problem is to specify the coefficient predicates
and prove injectivity for every malformed certificate while retaining one
nonsurjective fiber. The translation lets that problem be designed as a
computer with conditional linear updates and then encoded algebraically.
No such update rule is currently exhibited.

`finite-pattern-orbit-closure-forces-surjunctivity` supplies a separate
test for genuinely nonlinear rules. If the encoder and a decoder preserve
the span of constants and finitely many rational pattern-monomial orbits
containing all one-site observables, the encoder must be surjective over
every group. Those nonconstant pattern orbits are projective modules over
Q[G], where stable finiteness is known in characteristic zero.

A proposed finite verification loop must therefore distinguish a finite
description from finite closure of its pattern observables: they are not
the same condition. A counterexample necessarily has unbounded orbit
growth under this closure process, but an explicit reversible two-track
rule already has such growth, so growth by itself proves nothing. The
remaining task is still to construct a strict full-shift embedding and
prove injectivity on every configuration.

The direct finite-difference extension of the certificate-linear route
also fails: `boolean-secants-do-not-supply-operator-left-inverses` gives
a reversible three-bit gate whose canonical telescoping secant is
singular. Encoder-decoder inversion recovers the actual difference of
two inputs, but it does not provide a matrix inverse on arbitrary data
with those inputs held as certificates. Ordinary formal derivatives
do not fix the gap, since they do not descend to the Boolean function
algebra. These are restrictions on those specific linearization methods,
not a proof against all nonlinear computation routes.

The locality issue has a positive stabilized answer in
`injective-automata-have-local-stable-secant-dilations`: two local
additive shears and a track swap give an explicit reversible operator
carrying each genuine input difference to its output difference. This
implements the proposed preservation of an error syndrome. The remaining
condition is precise: the syndrome must vanish on every arbitrary data
vector with the certificate fixed, not just on the certified execution
difference. That condition is QP=I. Without it the ambient construction
is reversible and has no missing configuration; with it a strict
zero-auxiliary restriction requires the further reverse defect PQ!=I.
No such pair is currently produced.
