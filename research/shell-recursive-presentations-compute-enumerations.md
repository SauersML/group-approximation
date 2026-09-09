---
rg: 2
id: shell-recursive-presentations-compute-enumerations
kind: claim
title: A recursive presentation of a shell group computes its regular enumeration and the input word problem
artifacts:
  - research/artifacts/boone-higman-shell-effective-presentation-2026-09-08.md
---

Fix an infinite finitely generated P, a finite generating set S, and
nu:P->N. Use the shell group E_nu and its one-singularity stabilizer
A_1. If either group admits a recursive presentation, then the word
problem of P is decidable and nu is computable on S-words. Its inverse
can also be computed as a word representing the element at a given index.

The extraction is uniform given the recursive presentation, words
marking the shell generators hat(S) and three specified elements of V,
and the integer nu(1_P). The word-problem extraction does not require
that last integer. The marked presentation is assumed correct; the
algorithm does not recognize whether a proposed presentation is correct.

Consequently every successful enumeration in the OPEN universal
shell-stabilizer claim is computable. This does not provide a uniform
procedure that finds a successful enumeration from a presentation of P.
Computability of nu is not asserted sufficient for any shell presentation.

More generally, any fixed countable abstract group is isomorphic to
E_nu for at most countably many nu, and likewise for A_1. For fixed P,
each family therefore has continuum many abstract isomorphism classes.
