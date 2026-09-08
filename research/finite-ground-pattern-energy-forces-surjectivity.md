---
rg: 2
id: finite-ground-pattern-energy-forces-surjectivity
kind: claim
title: Finitely many zero-energy phases suffice for arbitrary-group surjectivity
distinct_from:
  finite-injective-pattern-energy-forces-surjectivity: that requires the vacuum to be the only simultaneous zero-energy configuration; this permits any finite zero-energy subshift and uses nonamenable expansion when a fixed detection radius is unavailable.
  finite-injective-charge-noncreation-forces-surjectivity: that uses positive charges on individual nonzero symbols; this allows overlapping interactions with several zero-energy phases.
artifacts:
  - research/artifacts/finite-ground-energy-and-compiler-obstruction-2026-09-08.md
---

Let G be any group, A a finite alphabet with vacuum 0, and tau:A^G->A^G
a cellular automaton fixing 0^G and injective on finite-support
configurations. Let e:A^P->[0,infinity) be a finite-range density with
e(0^P)=0. For finite-support x put

    E(x)=sum_g e((x(gp))_(p in P)).

Suppose E(tau(x))<=E(x) for all such x and the simultaneous zero locus

    Z_e={x:e((x(gp))_(p in P))=0 for every g}

is finite. Then tau is surjective on the full shift A^G.

On a nonamenable G the conclusion is stronger: E is conserved on all
finite configurations and tau permutes each finite energy sector.
The proof in that case also works with an infinite Z_e if there is a
nonamenable subgroup H such that every z in Z_e satisfies
z(gh)=z(g) for all g in G and h in H.

The finite-phase hypothesis is strictly weaker even as an existence
condition on the automaton. The reversible rule over Z

    tau(a,b)_i=(a_i+b_i,b_(i+1))                     (over F_2)

preserves the local density

    e_i=1_(a_i+a_(i+1)+b_i != 0)+1_(b_i != 0).

Its simultaneous zero locus consists of the two constant
configurations (0,0)^Z and (1,0)^Z. Yet an isolated b produces support
size n+1 after n steps, so no nonincreasing nonnegative local energy
with singleton zero locus can exist for this automaton.

This establishes a larger restricted surjectivity class. It does not
construct an energy for arbitrary injective automata or close the
unrestricted Gottschalk root.
