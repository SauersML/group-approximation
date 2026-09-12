---
rg: 2
id: split-ca-quantization-has-sharp-defect
kind: claim
title: Strict cellular sections have a nonlocal range projection and a maximal quantum multiplicative defect
distinct_from:
  split-decoders-have-generic-cantor-fibers: that packs classical alternatives in decoder fibers; this computes operator-norm obstructions for quantizing the encoder.
  finite-pattern-orbit-closure-forces-surjunctivity: that assumes a finite invariant rational observable module; this analyzes full matrix observables and distinguishes completely positive compression from a homomorphism.
artifacts:
  - research/artifacts/gottschalk-quantum-compression-2026-09-07.md
---

Let G be infinite and let tau:B^G -> A^G, sigma:A^G -> B^G be cellular
maps on finite nonempty alphabets with sigma tau=id. Use constant
backgrounds b and c=tau(b), and let V map the finite-configuration basis
vector |x> to |tau(x)>. Then V is an isometry. Let P=VV* and let A_G,
B_G be the norm closures of the full finite-region matrix algebras.

Compression Phi(O)=V*OV is a unital completely positive contraction
A_G -> B_G. For memories N,M of tau,sigma containing the identity,
Phi sends operators supported in F to operators supported in
F M^(-1) N^(-1) N.

If tau is strict, dist(P,A_G)=1/2 and there is a finite-region unitary
Q with norm(Phi(Q*Q)-Phi(Q*)Phi(Q))=1. If tau is onto, Phi is an
isomorphism with a local inverse. A unital *-homomorphism extending the
diagonal pullback f -> f composed with tau exists exactly in the onto
case, even if locality is not required of that extension.

These facts identify the obstruction to applying finite-algebra reasoning
to the automatically constructed local compression. They do not show
that a strict equal-alphabet encoder exists or that it is impossible.
