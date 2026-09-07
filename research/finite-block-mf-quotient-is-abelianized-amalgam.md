---
rg: 2
id: finite-block-mf-quotient-is-abelianized-amalgam
kind: claim
title: The exact MF quotient of a finite-block group is an amalgam with the abelianized lamp
distinct_from:
  finite-block-perfect-lamps-have-exact-mf-radical: That treats perfect finite lamps and has residually finite quotient V; this classifies the quotient for every finite lamp group.
artifacts:
  - research/artifacts/finite-block-perfect-mf-radicals.md
---

With Gamma, alpha, V, Gamma+, X, Y and p as in the finite-block perfect-lamp
theorem, let K be any finite group. For

    G_K = ( *_(y in Y) product_(x in p^-1(y)) K_x ) semidirect V,

the canonical blockwise abelianization map q_K has MF target and

    Rad_MF(G_K) = ker(q_K),
    G_K/Rad_MF(G_K) ~= V *_(Gamma+) (Gamma+ x K_ab).

Section 3 of the artifact proves the lower inclusion by finite-dimensional
fixed-algebra transport and the upper inclusion by a normal-form embedding
into a residually finite group's symmetric double. Its use of Shulman's
Theorem 10 is explicitly C-star-algebraic, with the regular-trace argument
that verifies the group embedding.
