---
rg: 2
id: lef-elementary-groups-force-lef-rings-proof
kind: route
title: Extend a finite model through the finitely presented Steinberg cover of a free ring, then read off the level ideal
target: lef-elementary-groups-force-lef-rings
requires:
  - steinberg-finite-presentation-and-kazhdan-theorem
artifacts:
  - research/artifacts/un-lef-converse-2026-09-13-part1.md
---

Full proof: artifact §1. Fix a finite window `W ⊆ R` containing `0` and `1` and closed under negation.

1. **Cover.** Let `A = Z<x_r : r ∈ W>` be the free unital ring and `pi : A -> R`, `x_r |-> r`. `A` is finitely
   presented, so `St_N(A)` has a finite presentation `<S | Rel>` on `S = {x_ij(1)^(±1), x_ij(x_r)^(±1)}`
   (import; `S` generates, by the commutator relations and products). Let `theta : St_N(A) -> EL_N(R)`,
   `x_ij(a) |-> e_ij(pi(a))`.
2. **Ball.** Put `L = {0, 1, x_r, x_r + x_s, x_r x_s}` and `D = L - L`. Fix words `u_c` in `S` for `x_13(c)`,
   `c ∈ D`. Let `B` be the finite set of theta-images of `S`, of all relator prefixes, and of all prefixes of the `u_c`.
3. **Homomorphism.** LEF gives an injective partial homomorphism `psi : B -> Q`, `Q` finite. Setting
   `rho(s) = psi(theta(s))` and inducting along prefixes, each relator evaluates to `psi(1) = 1`. So `rho`
   extends to a homomorphism `St_N(A) -> Q` with `rho(x_13(c)) = psi(e_13(pi(c)))` for `c ∈ D`.
4. **Level ideal.** `K_ij = {a : rho(x_ij(a)) = 1}` are additive subgroups.
   - `[x_ij(a), x_jk(1)] = x_ik(a)` and `[x_ij(1), x_jk(a)] = x_ik(a)` give the cycle
     `K_12 ⊆ K_13 ⊆ K_23 ⊆ K_21 ⊆ K_31 ⊆ K_32 ⊆ K_12`, and every `K_ij` equals one `K`.
   - `[x_12(a), x_23(b)] = x_13(ab)` makes `K` a two-sided ideal.
   - `A/K ≅ rho(x_13(A))` is finite.
5. **Window.** For `c ∈ D`, `c ∈ K` iff `pi(c) = 0`, by injectivity of `psi` on `B`. So `r |-> [x_r]` is an
   injective map `W -> A/K` preserving `0`, `1`, negatives, and the sums and products that stay in `W`. ∎

Recalled, not re-derived: Tietze moves. The import is `steinberg-finiteness-kazhdan-citation`
(Ershov–Jaikin-Zapirain 0809.4095v2 §6.1, citing Krstić–McCool Theorem 3).
