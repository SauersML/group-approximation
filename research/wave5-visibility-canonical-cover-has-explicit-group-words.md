---
rg: 2
id: wave5-visibility-canonical-cover-has-explicit-group-words
kind: claim
title: The exact canonical K7 cover has a six-generator twenty-four-relator group presentation with an explicitly marked central word
distinct_from:
  wave4-visibility-k7-marked-face-presentation: That gives an abstract free product of finite vertex kernels with marked face relations; this expands every corner into concrete integer group words for exact finite-group algorithms beyond the Lazard range.
artifacts:
  - research/artifacts/hyperbolic-rf-wave5-visibility-2026-09-20.md
  - experiments/hrf-wave5-pquotient-2026-09-20/pquotient.g
---

Let u_j,v_j, j=0,1,2, generate the three vertex kernels; put
w_j=[u_j,v_j]. Use u_j^7=v_j^7=1 for all j, w_0=1, and
w_j^7=[w_j,u_j]=[w_j,v_j]=1 for j=1,2. Set, with exponents mod7,

    C_i=(u_0^i v_0^(3i^2))
        (u_1^i v_1^(3i^2) w_1^(6i^3))
        (u_2^i v_2^(3i^2) w_2^(5i^3)).

The full integral extension B_c0 is presented by these thirteen
vertex relators, the five equations C_i=C_1 for i=2,...,6, and
centrality of C_1 against all six generators. Its marked infinite
central generator is z=C_1^-1. No z^7 relation is imposed.

The presentation is valid for arbitrary group targets; modular
exponents are justified solely inside the finite vertex groups.

DERIVATION
wave5-visibility-explicit-group-word-proof
