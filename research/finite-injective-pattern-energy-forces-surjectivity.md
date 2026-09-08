---
rg: 2
id: finite-injective-pattern-energy-forces-surjectivity
kind: claim
title: A finite-injective automaton cannot dissipate a nonnegative pattern energy whose only zero configuration is the vacuum
distinct_from:
  finite-injective-charge-noncreation-forces-surjectivity: that uses strictly positive charges on individual nonzero symbols; this allows zero-valued nonvacuum local patterns and overlapping finite-range interactions, provided the simultaneous zero-energy locus is the vacuum.
  finite-pattern-orbit-closure-forces-surjunctivity: that requires a finite invariant rational observable module for an encoder and decoder; this uses a nonincreasing nonnegative local energy and needs no decoder or finite pullback closure.
artifacts:
  - research/artifacts/pattern-energy-collision-proof-2026-09-08.md
---

Let A be a finite alphabet with distinguished symbol 0, G any group,
and tau:A^G->A^G a cellular automaton fixing 0^G and injective on
configurations with finite support relative to 0. Let P contain 1_G
and be finite, and let e:A^P->R be nonnegative with e(0^P)=0. Write

    e_g(x)=e((x(gp))_(p in P)),
    E(x)=sum_(g in G) e_g(x)

for finite-support x. Suppose

    {x in A^G : e_g(x)=0 for every g in G} = {0^G},       (PE1)
    E(tau(x)) <= E(x) for every finite-support x.        (PE2)

Then E(tau(x))=E(x) for every finite-support x, tau permutes each
finite-support energy level bijectively, and tau is surjective on A^G.
The group need not be amenable, sofic, finitely generated, or torsion-free.

Condition (PE1) is on all configurations. Compactness makes it
equivalent to a finite detection statement: there is a finite D such
that every occupied site is within a right translate of D of a center
with positive local energy. Consequently each energy sector admits a
finite token encoding that remembers the entire configuration.

This strictly extends the available positive single-site charge test.
On two binary tracks over Z, let

    rho(a,b)_i=(a_i XOR b_(i+1), b_i),
    S(a,b)_i=(b_i,a_i),
    tau=rho S rho.

The nonnegative density e_i(x)=1_(rho(x)_i != (0,0)) has (PE1) and is
conserved by tau. But an isolated (1,0) maps to a (1,0) at -1 and a
(0,1) at 0, strictly increasing every charge positive on all nonzero
single-site symbols. The example is reversible and demonstrates the
strict change in hypotheses; it is not a nonsurjunctive automaton.

For a strict full-shift encoder with quiescent vacuum, every local
energy satisfying (PE1) must increase on some finite input. This rules
out a larger family of conserved local syndrome constructions in the
Leavitt-unit-group nonsurjunctivity lane. No such counterexample, and
no unrestricted surjunctivity theorem, follows from this result.
