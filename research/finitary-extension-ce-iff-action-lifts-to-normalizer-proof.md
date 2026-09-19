---
rg: 2
id: finitary-extension-ce-iff-action-lifts-to-normalizer-proof
kind: route
title: Conjugate the embedding of R to the diagonal one and read the group unitaries in the normalizer
target: finitary-extension-ce-iff-action-lifts-to-normalizer
requires: []
artifacts:
  - notes/HYPERLINEAR_NONSOFIC_ATTEMPT_2026-08-26.md
---

**Surjectivity of `Ad`.**  By Connes' theorem every `beta in Aut(R)` is a
pointwise `||.||_2`-limit of inner automorphisms `Ad(v_n)`, `v_n in U(R)`.
Then `u = (v_n)_omega in U(R^omega)` satisfies `u x u^* = beta(x)` for all
`x in R`, so `u in N` and `Ad(u)|_R = beta`.  The kernel of `Ad` is the set of
unitaries of `R^omega` commuting with `R`, i.e. `U(R' cap R^omega)`.

**(2) => (1).**  Given `u`, define `Theta(x lambda_g) = x u_g` on the
algebraic crossed product `R rtimes_alg G`.  It is multiplicative:
`(x lambda_g)(y lambda_h) = x alpha_g(y) lambda_(gh)` and
`x u_g y u_h = x alpha_g(y) u_g u_h = x alpha_g(y) u_(gh)`; it is
`*`-preserving since `u_g^* = u_(g^(-1))`.  The trace condition gives
`tau(Theta(x lambda_g)) = delta_(g,1) tau(x)`, which is the canonical trace of
the crossed product, so `Theta` is trace-preserving and extends to a normal
injective `*`-homomorphism of the `II_1` factor `R rtimes_alpha G` into
`R^omega`.

**(1) => (2).**  Let `Theta: R rtimes_alpha G -> R^omega` be trace-preserving.
Its restriction to `R` is a trace-preserving embedding of `R`.  Any two
trace-preserving embeddings of `R` into `R^omega` are unitarily conjugate:
write `R` as the closure of an increasing union of matrix algebras `M_(2^n)`;
two embeddings agree up to a unitary on each `M_(2^n)` (matrix algebras with
equal traces of minimal projections are conjugate in a `II_1` factor), and a
diagonal argument along `omega` produces one unitary of `R^omega` conjugating
the two embeddings on all of `R` (this is the easy direction of Jung's
characterization of `R`).  After conjugating, `Theta|_R` is the diagonal
embedding, and `u_g = Theta(lambda_g)` lies in `N`, implements `alpha_g`, and
satisfies `tau(x u_g) = tau(Theta(x lambda_g)) = 0` for `g != 1`.

**Outer actions.**  Let `E: R^omega -> R` be the trace-preserving conditional
expectation and `a = E(u_g)`.  For `y in R`,
`a y = E(u_g y) = E(alpha_g(y) u_g) = alpha_g(y) a`.  Then `a^* a` commutes with
`R`, hence is a scalar `c >= 0`; if `c > 0`, `v = c^(-1/2) a` is an isometry
in the finite factor `R`, hence a unitary, and `alpha_g = Ad(v)` is inner.
So for outer `alpha_g`, `a = 0` and `tau(x u_g) = tau(x E(u_g)) = 0` for all
`x in R`.  Thus for outer actions condition (2) reduces to the existence of a
homomorphic lift, which is the same as a homomorphic section of the pullback
extension `E_alpha = {(g, w) in G x N : Ad(w)|_R = alpha_g} -> G`.

**Calibrations.**  For the trivial action, `E_alpha = G x U(R' cap R^omega)`
and the trace condition asks for a homomorphism `G -> U(R' cap R^omega)` with
`tau(u_g) = 0` for `g != 1`; since `R' cap R^omega` contains
`(1 tensor R)^omega` under `R ~= R tensor R`, hence a copy of `R^omega`, this
is equivalent to hyperlinearity of `G`.  For `G = F_n` free, choose any lifts
of the generators and extend freely.
