---
rg: 2
id: finite-pattern-orbit-closure-forces-surjunctivity
kind: claim
title: A finite invariant family of rational pattern observables forces a full-shift encoder to be surjective
distinct_from:
  certificate-controlled-routing-is-surjunctive: that treats data routing with preserved certificates; this permits arbitrary nonlinear local rules subject to a different finite observable-closure condition.
  certificate-linear-automata-have-local-linear-decoders: that constructs a decoder linear in a data track; this concerns arbitrary finite alphabets and the rational pullback action on local functions.
  finite-subgroup-copy-circuits-have-no-recurrent-branching: that constrains projective copying equations in positive characteristic; this uses the characteristic-zero projectivity of finite pattern orbits to constrain encoder-decoder pairs.
---

Let A be a nonempty finite alphabet, G any group, and tau,sigma:A^G->A^G cellular
automata with sigma tau=id. Fix a rational basis

    {1,psi_1,...,psi_(|A|-1)} of the functions A->Q.

A nonconstant pattern monomial is a finite product of the psi_i evaluated
at distinct sites, with nonempty site support. Let W be the rational span
of 1 and finitely many G-translation orbits of these basis monomials.
Suppose W contains every one-site psi_i observable and is invariant under
both pullbacks tau^*:f->f composed with tau and sigma^*.

Then tau sigma=id as well. In particular tau is surjective.

An injective cellular automaton on a finite-alphabet full shift always
admits some local decoder sigma. Therefore any hypothetical injective
nonsurjective tau must, for every local decoder, generate infinitely many
distinct pattern-monomial orbits when one repeatedly expands the two
pullbacks starting from the one-site observables.

This necessity is not sufficient for a counterexample. Already over Z the
reversible binary two-track rule

    tau(a,b)_j=(a_j XOR b_j, b_(j+1))

has unbounded rational pattern growth. Its inverse is

    sigma(a,b)_j=(a_j XOR b_(j-1), b_(j-1)).

The condition concerns closure of rational observables modulo translation,
not merely a finite gate list, finite memory, or a finite cyclic verifier
description. It does not prove surjunctivity of arbitrary cellular automata.

The quantitative extension is
`split-ca-defects-force-linear-observable-rank`: a strict encoder has a
defect tower of dimension exactly n delta, giving a lower bound on the
unsaturated observable span. Bounded finite-orbit closure is recovered as
a special case. `reversible-xor-has-linear-observable-rank` computes the
displayed example's rank exactly as 2n+3 and explains why a universal
sublinear upper bound cannot complete the argument.
