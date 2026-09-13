---
rg: 2
id: o2-multiplier-extension-k1-injective-iff-unitization
kind: claim
title: An ideal with a unital O_2 in its multiplier algebra gives a properly infinite algebra that is K1-injective iff the ideal's unitization is
artifacts:
  - research/artifacts/lxi-o2-multiplier-reduction-2026-09-12.md
---

Let `I` be a non-unital C\*-algebra, and let `S_1, S_2 ∈ M(I)` be isometries with
`S_1S_1^* + S_2S_2^* = 1`. Put `A = C*(I, S_1, S_2) ⊆ M(I)`. Then `A` is unital and properly infinite,
`A/I ≅ O_2`, and `A` is K1-injective if and only if the unitization `Ĩ` is K1-injective. More precisely,
a unitary of `Ĩ` lies in `U_0(A)` iff it lies in `U_0(Ĩ)`.

So a counterexample to STW Problem LXI follows from any non-unital `I` with a unital copy of `O_2` in
`M(I)` whose unitization fails K1-injectivity. Such an `I` may be stably finite. Conversely, LXI implies
that all these unitizations are K1-injective.

The proof uses three inputs. The quotient map `U_0(A) → U_0(O_2)` is a principal bundle, by
Bartle--Graves local sections and Hurewicz. `π_1(U(O_2)) = K_0(O_2) = 0`, by Jiang for the Z-stable
algebra `O_2`. And `K_1(I) → K_1(A)` is injective, because `K_0(O_2) = 0`.
