---
rg: 2
id: k1-injectivity-extends-over-properly-infinite-quotients
kind: claim
title: An extension with K1-injective unitized ideal and properly infinite K1-injective quotient is K1-injective
artifacts:
  - research/artifacts/lxi-halving-homotopy-and-extensions-2026-09-12.md
---

Let `A` be a unital C\*-algebra and `I ⊴ A` a closed ideal. Suppose `A/I` is properly infinite and
K1-injective, and the unitization `Ĩ = I + C1 ⊆ A` is K1-injective. Then `A` is K1-injective.

The proof has two ingredients. Every class in `K_0(A/I)` is the class of a projection `e ∈ A/I` (Cuntz). The
exponential map sends `[e]` to `[exp(2πih)]` for a self-adjoint lift `h`, and that unitary lies in
`U_0(A)`. So the obstruction coming from the connecting map is realized inside the identity component.

Consequences for STW Problem LXI. A counterexample cannot be an extension of a K1-injective properly
infinite algebra (for instance a Kirchberg algebra) by an ideal whose unitization is K1-injective.
Two cases are fully justified here. First, stable ideals: a unitary of `Ĩ` moves into some
`M_n(J)~` for `I ≅ J ⊗ K`, and its matrix null-homotopy transports back through a corner embedding.
Second, ideals whose unitization has stable rank one (Rieffel, Proc. London Math. Soc. 46 (1983),
Theorem 10.12). Real rank zero ideals are covered provided one accepts Lin's theorem that unital real
rank zero algebras are K1-injective. It is quoted as [Lin01, Corollary 4.2.10] in Blanchard
arXiv:0804.4624v13, proof of Proposition 3.2, and it applies because the real rank of `I` is by
definition that of `Ĩ`. That citation was not checked against Lin's book. Z-stable ideals are not
claimed: Jiang's theorem is for unital algebras, and `Ĩ` is not Z-stable. Now let `T(E)` be a unital
Toeplitz--Pimsner algebra whose Fock module is isomorphic to `H_B`, so that its compact ideal is stable,
and whose Cuntz--Pimsner quotient is properly infinite. Then `T(E)` is K1-injective as soon as that
quotient is.
