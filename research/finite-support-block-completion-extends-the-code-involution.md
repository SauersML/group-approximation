---
rg: 2
id: finite-support-block-completion-extends-the-code-involution
kind: route
title: Complete the projected code involution by the identity on unused finite blocks
target: balanced-invariant-code-has-a-reversible-full-shift-extension
requires: []
artifacts:
  - research/artifacts/gottschalk-finite-support-reversible-completion-of-invariant-code-2026-09-08.md
---

The swap after the prefix map has order four. Its inverse r
exchanges the two disjoint predicates supporting conditional
V_4 actions and commutes with every global diagonal A_4 action.
Those conditional actions form V_4 x V_4, normalized by r and
the order-three diagonal s. Hence H=<s,k,r> has at most 192
elements and contains all addresses of the code's linear extension.

Project the invariant code to P_H in F_2^H. The finite block
rule preserves P_H and squares to the identity there, because
the original rule is an involution on the code. Extend it by
the identity on the complement of P_H. Both pieces are invariant
under the left H action, so the resulting block permutation
glues to a reversible full-shift cellular automaton on left cosets.
Projection injectivity and independent realizability of code
blocks are not assumed.

A nonzero four-term annihilator places P_H in a proper linear
subspace; the completed permutation fixes that subspace's entire
complement but is nonidentity. This proves that the completion
is nonlinear. The same annihilator, used as a linear feedback
correction, preserves all complement collisions of the two-term
rule, leaving other linear-feedback corrections unresolved.
