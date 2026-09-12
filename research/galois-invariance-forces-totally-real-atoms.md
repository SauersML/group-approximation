---
rg: 2
id: galois-invariance-forces-totally-real-atoms
kind: claim
title: Galois-invariant kernel dimensions force every algebraic atom of an integral self-adjoint matrix to be totally real
distinct_from:
  galois-invariance-implies-algebraic-eigenvalues: that uses invariance under the automorphisms of C fixing Qbar to exclude transcendental eigenvalues; this uses the action of Gal(Qbar/Q) on the eigenvalue itself and constrains the algebraic ones, which that claim leaves untouched.
  finite-spectrum-integral-elements-obey-determinant: that proves equal conjugate masses unconditionally, for every group, under the hypothesis that the spectrum is finite; this assumes Galois invariance instead and needs no spectral hypothesis, and it adds total reality.
  vn-rank-galois-invariant-for-torsion-free-groups: that is the open invariance statement for automorphisms of C fixing Qbar; this is a consequence of invariance under the automorphisms that move algebraic numbers.
---

Let `G` be a group whose von Neumann kernel dimensions are Galois invariant:
for every `B in M_n(Qbar[G])` and every `sigma in Gal(Qbar/Q)`,

```text
dim_(N(G)) ker r_(sigma(B)) = dim_(N(G)) ker r_B,
```

where `sigma(B)` applies `sigma` to every coefficient. Let `A in M_n(Z[G])` be
self-adjoint and let `lambda` be an atom of its spectral measure,
`mu_A({lambda}) = dim_(N(G)) ker(r_A - lambda) > 0`. If `lambda` is algebraic,
then

1. `lambda` is **totally real**: every root of its minimal polynomial over `Q`
   is real; and
2. `mu_A({sigma lambda}) = mu_A({lambda})` for every `sigma in Gal(Qbar/Q)`.

No rationality of the mass is asserted, and none is available: sofic groups
satisfy the hypothesis and can still have irrational, even transcendental,
`mu_A({lambda})` (Austin; Grabowski). Balance and rationality are independent.

**ESTABLISHED** by [[galois-invariance-totally-real-atoms-proof]].

The contrapositive is the useful direction. A self-adjoint integral matrix with
an atom at a real algebraic number that has a non-real conjugate refutes Galois
invariance for its group; over a sofic group no such matrix exists
([[sofic-groups-have-totally-real-algebraic-atoms]]), so such an atom certifies
nonsoficity ([[non-totally-real-atom-certifies-nonsoficity]]).

The degree of the atom is what carries the content. Rational atoms say nothing,
and a real quadratic irrational is automatically totally real, so the first
testable case is degree three: an atom at a root of `x^3 - x - 1`, or at
`2^(1/3)`, whose other two conjugates are complex.
