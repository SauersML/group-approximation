---
rg: 2
id: o2-quotient-extension-ideal-k1-injective-iff-algebra
kind: claim
title: In an extension of O_2 by I, the unitization of I is K1-injective iff the middle algebra is
distinct_from:
  o2-multiplier-extension-k1-injective-iff-unitization: that needs a unital O_2 in M(I) and treats B = I + O_2; this assumes only B/I ≅ O_2, so it covers ideals with unital quotients of nonzero unit class, where no such O_2 exists.
artifacts:
  - research/artifacts/k1-defect-ideal-o2-quotient-lifting-2026-09-13.md
  - research/artifacts/k1-defect-ideal-z-stable-quotients-2026-09-13.md
---

Let `B` be a unital C\*-algebra and `I` a closed ideal with `B/I ≅ O_2`. Put `I~ = I + C1 ⊆ B`. Then:

- (a) `U(I~) ∩ U_0(B) = U_0(I~)`;
- (b) `K_*(I) -> K_*(B)` is an isomorphism;
- (c) `I~` is K1-injective iff `B` is K1-injective;
- (d) if `K_1(B) = 0`, then `U(I~)` is path-connected iff `B` is K1-injective.

More generally, (a) holds for any quotient `Q = B/I` whose based loop space `U((SQ)~)` is path-connected.
(a)–(c) hold verbatim, with (b) weakened to injectivity on `K_1`, whenever Q is unital, Z-stable and
properly infinite with `K_0(Q) = 0`, for example `O_2 ⊗ C(T)` (artifact part 2, Corollary 3').

- Application: the halving homotopy holds iff `J_c~` is K1-injective, for `J_c = ker(O_2 * C(T) -> O_2 ⊗ C(T))`.
- Application: LXI holds iff `U(I_c~)` is connected, for `I_c = ker(T_2 * T_2 -> O_2 ⊗ C(T))`.

Consequences, in `toeplitz-defect-ideal-connected-iff-extension-k1-injective`:
- STW Problem LXI forces the Toeplitz defect ideal `J` of `T_2 * T_2` to have connected `U(J~)`.
- LXI is equivalent to connectivity of `U(I_f~)`, where `I_f = ker(T_2 * T_2 -> O_2)`.
