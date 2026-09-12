---
rg: 2
id: deligne-cover-linear-soficity-is-rank-projective-approximation
kind: claim
title: Deligne's triple cover is linear sofic in characteristic p exactly when its multiplier has rank-approximate projective representations
distinct_from:
  deligne-sector-gap-is-exactly-nonhyperlinearity: that is the normalized Hilbert--Schmidt version, for unitary almost representations and hyperlinearity; this is the rank-metric version over finite fields of characteristic p != 3, for linear soficity, and it feeds stable finiteness of the twisted group algebras.
  growing-rank-decoder-is-linear-soficity: that identifies faithful growing coefficient decoders of k[G] with algebra linear soficity; this reduces group linear soficity of one central extension to projective almost representations of the quotient, with no separation condition.
artifacts:
  - research/artifacts/deligne-twisted-group-algebras-2026-09-12.md
---

Let `1 -> <z> = Z/3 -> E_3 -> Gamma = Sp_4(Z) -> 1` be Deligne's triple cover, with section cocycle `a` and a
primitive cube root of unity `w`. Let `p != 3` be prime. The following are equivalent:

1. `E_3` is `F_p`-linear sofic.
2. For some `j in {1, 2}`, and then for both, the multiplier `w^(j a)` has **rank-approximate projective
   representations in characteristic `p`**. That means: for every finite `B <= Gamma` and `eps > 0` there are a
   finite field `F` of characteristic `p` containing `w` and `rho : B -> GL_d(F)` with
   `rank(rho(g)rho(h) - w^(j a(g,h)) rho(gh)) <= eps d` whenever `g, h, gh in B`.

No separation condition is imposed in 2.

**Payoff.**
- **Stable finiteness.** Through `linear-sofic-group-algebra-is-stably-finite`, condition 2 makes `F[E_3]`
  stably finite for every field of characteristic `p`. So both twisted group algebras of `Gamma` are stably
  finite, and `E_3` carries no strict linear automaton in characteristic `p`.
- **Contrapositive.** A one-sided invertible pair in a twisted group algebra of `Gamma` in characteristic
  `p != 3` makes `E_3` a non-linear-sofic group.

**ESTABLISHED 2026-09-12** by `deligne-cover-rank-projective-approximation-proof` (artifact Theorem 2.1).
Verification requested from w4-vf-linear-b.
