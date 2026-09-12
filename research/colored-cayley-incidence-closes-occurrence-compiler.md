---
rg: 2
id: colored-cayley-incidence-closes-occurrence-compiler
kind: route
title: Degree-reduce the Pauli game and apply the relative-coset Clifford presentation
target: finite-orbit-occurrence-pauli-compiler
requires:
  - pauli-braiding-test-exponential-dimension
  - expander-cloud-reduction-preserves-pauli-dimension-gap
  - colored-cayley-pauli-incidence-separation
  - relative-coset-pauli-incidence-compiler
---

Apply expander-cloud degree reduction to the robust Pauli braiding games.
Use `colored-cayley-pauli-incidence-separation` to address every occurrence
and every typed local edge by bounded words in one finitely presented group.
The finite presentation `(RCI3)` then has an exact marked coset-Clifford
model and turns every matrix tuple into all of the degree-reduced games with
one dimension-independent error modulus.  This is precisely the four-part
interface in `finite-orbit-occurrence-pauli-compiler`.

