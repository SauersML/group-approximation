---
rg: 2
id: fournier-facio-regular-models-carry-commutant-shift
kind: claim
title: Every nontrivial tracial model of the Fournier--Facio group carries a proper Hilbert-hotel shift on the Gamma-commutant
distinct_from:
  fournier-facio-hyperlinear-iff-singular-near: That identifies hyperlinearity with a purely singular free near state; this is a basis-free structural law that every nontrivial tracial model must satisfy, whether or not it comes from such a state.
  conjugate-commuting-perfect-copies-force-exponential-dimension: That bounds the dimension of exact finite-dimensional representations containing commuting conjugate perfect copies; this locates, in every finite von Neumann algebra model, the proper endomorphism and growing relative commutants produced by those copies.
artifacts:
  - research/artifacts/fournier-facio-hyperlinearity-survivor-audit-2026-09-11.md
---

**ESTABLISHED.**  Let `(M,tau)` be a finite von Neumann algebra with a
faithful normal tracial state, and let `u:G -> U(M)` be a nontrivial
homomorphism from the Fournier--Facio group.  With the notation of
`fournier-facio-group-contains-simple-wreath-shift`, put

```text
A = u(Gamma)' cap M,          theta(x) = u(t_1)^* x u(t_1).
```

Then `theta` is a normal unital trace-preserving injective *-endomorphism of
`A`, and

```text
theta(A) <= A cap u(J_0)',                                   (CS1)
u(J_-k) <= A,   theta(u(J_-k)) = u(J_-(k+1))      (k >= 0),  (CS2)
theta(A) != A,                                               (CS3)
theta^n(A)' cap A >= u(J_0 J_-1 ... J_-(n-1))''    (n >= 1). (CS4)
```

If moreover `tau(u(g))=0` for every `g!=1` (the regular character, e.g. a
hyperlinear model), then `u((+)_(k<=0) J_k)''` is the infinite tensor product
of copies of the II_1 factor `L(S)`, and `theta` acts on it as the shift.
Also `u(Gamma)''` contains `L(S)^(tensor n) tensor Ad(u(t_1))^n(u(Gamma)'')`
for every `n`, the tracial form of the self-similar tail (W7).

**Reading.**  A finite-dimensional algebra has no proper unital injective
endomorphism, and here `theta` is proper in every nontrivial model, with
relative commutants growing by one copy of `L(S)` at each iterate.  So no
argument that compares finite-dimensional commutants can be applied directly
to a normalized-HS model of `G`.  It must first exactify an unbounded tensor
tail at fixed precision.  This is the precise tracial place where the finite
counting behind nonsoficity has nothing to count.  The statement makes no
nonhyperlinearity claim.

Proof: `fournier-facio-commutant-shift-proof`.
