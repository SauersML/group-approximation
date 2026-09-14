---
rg: 2
id: signed-thompson-algebra-is-odd-measure-crossed-product-proof
kind: route
title: Fourier-transform the reflection group and read the evaluation at Dirac measures
target: signed-thompson-algebra-is-odd-measure-crossed-product
requires: []
artifacts:
  - research/artifacts/ternary-lift-signed-thompson-crossed-product-2026-09-12.md
---

**The subgroup.**
* `tau_C^2 = 1` and `tau_C tau_D = tau_(C triangle D)`.
* `C -> tau_C` is injective, because the diagonal of `R` is `C(X, F_3)`.
* `g P_C g^-1 = P_(gC)` for `g in V`.
* An element of `E cap V` commutes with every `P_D`, so it acts trivially on `X` and equals `1`.

**The algebra.**
* `E` is the direct limit of `F_2^P` over finite clopen partitions `P`, and `char F_3 != 2`. So
  `F_3[E] ~= C(Hom(E, +-1), F_3)`, and the characters are the finitely additive `F_2`-measures.
* `[z]` goes to `(-1)^(mu(X))`, so `eps_-` is the indicator of `M_-`.
* The split extension gives the algebraic crossed product.

**The evaluation.**
* `pi(q_C) = 4 P_C = P_C` matches `q_C(delta_x) = [x in C]`.
* The `q_C` generate `C(M_-, F_3)`, so `pi(f)` is `x -> f(delta_x)`.

**Surjectivity.**
* `S[alpha] T[beta] = S[alpha 0] T[beta 0] + S[alpha 1] T[beta 1]`, so nonempty `alpha`, `beta`
  suffice.
* A prefix replacement `[beta] -> [alpha]` extends to some `g in V`, and then
  `S[alpha] T[beta] = pi([g] q_[beta])`.

Theorem 2 of the artifact.
