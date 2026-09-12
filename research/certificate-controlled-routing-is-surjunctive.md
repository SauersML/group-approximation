---
rg: 2
id: certificate-controlled-routing-is-surjunctive
kind: claim
title: Certificate-controlled local routing cannot strictly embed a full shift over any group
distinct_from:
  subshift-self-embedding-carries-no-surjunctivity-content: that exhibits a subshift counterexample to a proposed implication; this proves surjunctivity of a specified class of full-shift rules over every group.
  finite-subgroup-copy-circuits-have-no-recurrent-branching: that concerns exact decompositions of projective modules with positive lifted trace; this concerns local data routing with arbitrary certificates and Bernoulli mass transport.
---

Let G be any group, A a finite alphabet with at least two symbols, B a
nonempty finite certificate alphabet, and r>=1. For each c in B^G, let
phi_c:G x {1,...,r}->G x {1,...,r} be a locally determined, equivariant
routing map of uniformly finite displacement. Define the cellular automaton

    E(x,c) = (y,c),    y(g,i) = x(phi_c(g,i)),

on (A^r x B)^G. Then E is injective if and only if it is surjective;
either condition makes every phi_c bijective.

The conclusion also permits a certificate-dependent permutation of A
applied to each read symbol. Finite compositions of these routing stages
and arbitrary reversible cellular automata, all acting on the same full
shift, likewise cannot be injective and nonsurjective. Different stages
may use different data/certificate decompositions of the site alphabet.

For r=1 there is an exact accounting identity under any full-support iid
certificate measure mu:

    mu{indegree_c(1)=0} = E_mu[(indegree_c(1)-1)_+].

Thus a collision on even one certificate forces an unread site on another
certificate. Locality makes both defects visible on finite patterns;
exceptional or malformed certificates cannot be discarded.

This restricts garbage-preserving computational constructions that factor
into the specified finite stages. It does not treat arbitrary nonlinear
local mixing, simultaneous cyclic constraints, or rules defined only on
a proper subshift. No general surjunctivity theorem is asserted.

The mass-transport principle is established mathematics; compare Murphy,
*Point-shifts of Point Processes on Topological Groups*, Proposition 2.2(j),
https://arxiv.org/abs/1704.08333. The route supplies the elementary finite-
memory proof and the full-shift and finite-composition consequences.
