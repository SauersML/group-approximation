---
rg: 2
id: fanizza-final-bcs-has-fixed-nonlinear-menu-citation
kind: route
title: Audit the explicit Section 5 constraints and the linear conjugacy gadget
target: fanizza-final-bcs-has-fixed-nonlinear-menu
requires:
  - fanizza-turing-bcs-signal-collapse
---

**Established by citation and finite truth-table audit.**  In arXiv:2510.04943
version 4, Proposition 5.13 writes the nested BCS explicitly.  Its proof names
`C13,C14` as equality of two conjunctions, `C17` as `O_D=O_P AND O_Q`, and
lists the unsatisfying assignments of `C18` as `A123 x A456`; the displayed
sets have cardinalities five and four and are exactly `(FNM1)` after the sign
to bit conversion.

The proof of Theorem 5.5 first retains every original BCS constraint and then
replaces each conjugacy relation by the gadget of Lemma 5.10.  The lemma states
that this gadget has 42 variables and 31 **linear** constraints of context
size at most three.  The proof identifies all its relations `(A0)--(A2)` as
linear.  Hence flattening adds no nonlinear predicate.  Direct evaluation of
the three displayed truth tables gives bad-atom counts `2,4,20`.

Source: Marco Fanizza et al., *The NPA hierarchy does not always attain the
commuting operator value*, arXiv:2510.04943v4, Section 5.1, Lemma 5.10 and
Section 5.2, Proposition 5.13.
