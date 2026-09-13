---
rg: 2
id: brr-commutator-criterion-null-unitary-citation
kind: route
title: Blanchard-Rohde-Rordam, Lemma 2.4(ii)
target: brr-commutator-criterion-null-unitary
requires: []
---

Source: E. Blanchard, R. Rohde, M. Rørdam, *Properly infinite C(X)-algebras and K_1-injectivity*,
arXiv:0704.1554v1 (12 April 2007). Read from the arXiv PDF, page 4, on 2026-09-13 by lane
ex3-k1-unit-axiom.

Verbatim: "Lemma 2.4 Let A be a unital C\*-algebra. [...] (ii) Let u be a unitary element A such that
[u] = 0 in K_1(A). Suppose there exists a projection p ∈ A such that ‖up − pu‖ < 1 and p and 1 − p are
properly infinite and full. Then u belongs to U^0(A)."

The missing "in" before "A" is in the source.

Their proof sets `x = pup + (1−p)u(1−p)`, so `||u − x|| < 1`, and polar-decomposes `x`. A symmetry
moves `1 − p` under `p`, which brings the unitary to the form `v_0 + (1 − p)` with `v_0 ∈ U(pAp)`.
They finish with "[13, Exercise 8.11]", the Rørdam--Larsen--Laustsen textbook; that exercise text was
not read. A self-contained version of the final step is
`isometry-compression-of-k1-trivial-unitary-is-null`.
