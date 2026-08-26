---
rg: 2
id: atomic-tracial-algebra-endomorphisms-are-automorphisms
kind: claim
title: A trace-preserving injective unital endomorphism of an atomic tracial von Neumann algebra is surjective
distinct_from:
  kazhdan-generated-amenable-algebra-is-atomic: that produces atomic algebras from Kazhdan groups; this is a rigidity statement about atomic algebras themselves, with no group in it.
  level-shift-obstruction: that is a Hamming-mass count for permutations shifting a graded set, an obstruction to one model architecture; this is a trace-mass statement about all trace-preserving self-embeddings of a countable direct sum of matrix algebras.
---

Let `P = (+)_(i in I) M_(n_i)(C)`, `I` countable, carry the faithful normal
tracial state `tau = sum_i lambda_i tr_(n_i)`, `lambda_i > 0`,
`sum_i lambda_i = 1`; write `mu_i = lambda_i / n_i` for the trace of a minimal
projection in the `i`-th block.

**Theorem.**  Every unital injective `*`-homomorphism `theta : P -> P` with
`tau o theta = tau` is surjective.  Equivalently: a unital von Neumann
subalgebra `Q <= P` with `(Q, tau|_Q)` trace-isomorphic to `(P, tau)` is all of
`P`.

There is no Hilbert hotel inside an atomic probability space: the trace
weights are a positive summable stationary vector for the Bratteli inclusion
matrix of `theta(P) <= P`, positive recurrence forces the inclusion to preserve
block sizes and be deterministic, and a deterministic self-map with a positive
finite stationary mass is a bijection.  The proof route carries the details.

The statement fails without atomicity: the hyperfinite `II_1` factor has
plenty of proper trace-preserving self-embeddings (`notes/OBSTRUCTIONS.md`,
Section 1, records `R x|_theta Z` compressing a subalgebra strictly), and this
is the "trace-blindness" that makes the tracial theory unable to see sizes.
Atomicity restores sizes: they are the minimal-projection traces `mu_i`, and
they are conserved.  This is the exact Hilbert--Schmidt counterpart of the
cell-size conservation in Kun--Thom's Theorem 4.1, and it is what
`amenable-kazhdan-models-absorb-compression` consumes.
