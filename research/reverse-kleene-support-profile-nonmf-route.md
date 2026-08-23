---
rg: 2
id: reverse-kleene-support-profile-nonmf-route
kind: route
title: Feed the authenticated qualitative compiler into reverse Kleene and Higman
target: reverse-kleene-support-profile-nonmf
requires:
  - authenticated-opnorm-challenge-compiler
  - threshold-free-reverse-kleene-mf-higman
---

The authenticated compiler supplies a uniformly recursively presented marked
group with HALT survival and NONHALT membership of the same word in the MF
radical.  Apply `threshold-free-reverse-kleene-mf-higman`: proof enumeration
forces the fixed machine not to halt, proves its marked word nontrivial, and
places that word in the MF radical.  Effective Higman embedding then produces
a finitely presented overgroup, which remains non-MF by subgroup heredity.

No property (T), asymptotic-commutant transport, central sign corner, Clifford
nontriviality witness, canonical trace, or implication from MF to
hyperlinearity enters this route.
