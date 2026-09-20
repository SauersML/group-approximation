---
rg: 2
id: directly-finite-ring-images-of-ca-monoids-kill-retracts
kind: claim
title: A homomorphism of the automaton monoid into a directly finite ring sends every automaton retract to the identity
distinct_from:
  surjunctivity-iff-automaton-monoid-directly-finite: that node is the equivalence between surjunctivity and direct finiteness of the monoid; this one is the criterion through representations into directly finite rings, with the K_0 form.
artifacts:
  - research/artifacts/automaton-monoid-intrinsic-sizes-2026-09-12.md
---

Let `G` be a group, `A` a finite alphabet, and `rho : CA(G;A) -> (S, ·)` a monoid homomorphism, or
anti-homomorphism, into the multiplicative monoid of a directly finite ring `S`.

- If `sigma o tau = id`, then `rho(tau o sigma) = 1`.
- So `G` is surjunctive on `A` as soon as some such `rho` has `rho(f) != 1` for every idempotent
  automaton `f != id`. Injective `rho` qualify.
- Directly finite targets include every ring with a faithful Sylvester rank function, such as rank
  ultraproducts.

K-theory form: in the monoid algebra `k[CA(G;A)]`, a strict pair makes `1 - tau o sigma` a nonzero
idempotent with class `0` in `K_0`, since `tau o sigma` is Murray–von Neumann equivalent to `1`. The
augmentation state vanishes on `1 - f` for every idempotent automaton `f`, so it never separates.

The natural representations (action on `A^G`, pullback on `C(A^G, k)`, pushforward on invariant
measures) separate idempotents but land in targets that are not directly finite, or they are measure
functionals. Restricted to linear automata over `F_p^n`, a separating `rho` proves `M_n(F_p[G])`
directly finite.

Proof: artifact Section 3, route `directly-finite-ring-images-kill-retracts-proof`.

## Attempts

- **Markov hull of the Koopman image** (swarm-0917 w22, 2026-09-20). Question: does direct finiteness
  survive in the smallest positive hull of the pullback representation? It does not, already on `Z`.
  - The xor automaton has an equivariant, faithful, Bernoulli-preserving, window-shrinking Markov section
    `T` with `T xor^* = 1` and `xor^* T != 1`. The same holds on every group with an element of infinite
    order (`stochastic-automaton-sections-do-not-force-injectivity`).
  - So representations that factor through equivariant Markov operators cannot separate idempotents.
    The idempotent `1 - xor^* T` has `K_0` class 0.
  - The relaxation with the Markov operator on the decoder side is equivalent to surjunctivity. A
    separating `rho` must therefore use multiplicativity of the encoder's image.
