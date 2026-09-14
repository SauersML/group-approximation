---
rg: 2
id: fournier-facio-invariant-mass-grows-along-compressor
kind: claim
title: In every regular tracial Fournier--Facio model the Gamma-invariant mass grows along the compressor and jumps from zero to one
invalidates:
  - fournier-facio-tracial-median-size-matching
distinct_from:
  fournier-facio-regular-models-carry-commutant-shift: That proves the compressor endomorphism of the Gamma-commutant is proper, a statement about algebras; this computes the frame-free invariant-mass functional that a tracial median size-matching step would have to conserve, and shows it is strictly monotone with jumps of size one.
  fournier-facio-one-compressor-subgroup-reduces-to-gamma: That locates every one-compressor argument inside <Gamma,t_1>; this shows why the ambient-(T) size-matching step of OpenAI's proof has no conservation law in normalized HS.
artifacts:
  - research/artifacts/fournier-facio-one-compressor-reduction-2026-09-11.md
---

**ESTABLISHED.**  Let `(M,tau)` be a finite von Neumann algebra with faithful
normal trace, and let `u:G -> U(M)` be a homomorphism from the
Fournier--Facio group with regular character, `tau(u(g))=0` for `g!=1`.  Put

```text
A = u(Gamma)' cap M,   theta(x) = u(t_1)^* x u(t_1),   F(x) = ||E_A(x)||_2^2.
```

1. **Monotone.**  `F(theta(x)) >= F(x)` for every `x in M`.
2. **Jump.**  For every `g in pi(S)\{1}`, `F(u(g)) = 0` and
   `F(theta(u(g))) = 1`.

So the invariant mass that a tracial version of OpenAI's median
size-matching step would use is not conserved along the compressor.  One
application of `theta` moves unit mass from the wandering sector of `Gamma`
(the simple factor `pi(S) <= Gamma`) into the invariant sector (its conjugate
`J_0`, which commutes with `Gamma`).  Permutation models conserve total
component mass because they count points.  The frame-free functional counts
nothing, and the drift here is not small, so ambient property (T) has nothing
to smooth.  This is the size-function form of the tracial Hilbert hotel.  By
`fournier-facio-one-compressor-subgroup-reduces-to-gamma` it is realized in
`R^omega` as soon as `Gamma` is hyperlinear.

Proof: `fournier-facio-invariant-mass-growth-proof`.
