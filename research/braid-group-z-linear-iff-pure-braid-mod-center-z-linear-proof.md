---
rg: 2
id: braid-group-z-linear-iff-pure-braid-mod-center-z-linear-proof
kind: route
title: Split the full twist off P_n and induce up to B_n
target: braid-group-z-linear-iff-pure-braid-mod-center-z-linear
requires:
  - torsion-free-virtually-z-linear-groups-are-z-linear
---

Classical inputs:

- (a) `B_n` is torsion-free, since the unordered configuration space of `n`
  points in the plane is a finite-dimensional `K(B_n, 1)` (Fadell–Neuwirth,
  Fox–Neuwirth).
- (b) `P_n` is the kernel of `B_n -> S_n`, so it has index `n!`.
- (c) `Delta^2 = (sigma_1 sigma_2 ... sigma_(n-1))^n` is central in `B_n`,
  since conjugation by `Delta` sends `sigma_i` to `sigma_(n-i)`.
- (d) Forgetting strands is a homomorphism of pure braid groups. Forgetting
  strands `3, ..., n` gives `phi: P_n -> P_2 = <sigma_1^2> ≅ Z`, and it sends
  the full twist on `n` strands to the full twist on 2 strands:
  `phi(Delta^2) = sigma_1^2`, a generator.

**Splitting.** Let `U_n = ker(phi)`. For `x in P_n` write `phi(x) = sigma_1^(2k)`.
Then `x Delta^(-2k) in U_n`, so `x = (x Delta^(-2k)) · Delta^(2k)` with the
second factor central. Also `U_n ∩ <Delta^2> = 1`, because
`phi(Delta^(2k)) = sigma_1^(2k) != 1` for `k != 0`. So `P_n = U_n × <Delta^2>` as an
internal direct product, and the quotient map restricts to an isomorphism
`U_n ≅ P_n / <Delta^2>`.

**(1) ⇒ (2) ⇒ (3).** Restrict an injective homomorphism `B_n -> GL_m(Z)` to
`P_n`, then to `U_n ≅ P_n / <Delta^2>`.

**(3) ⇒ (2).** Given injective `rho: U_n -> GL_m(Z)`, the block-diagonal map
`u · Delta^(2k) -> diag(rho(u), [[1, k], [0, 1]])` is an injective homomorphism
`P_n = U_n × Z -> GL_(m+2)(Z)`.

**(2) ⇒ (1).** `P_n` has index `n!` in the torsion-free group `B_n`, so
`torsion-free-virtually-z-linear-groups-are-z-linear` embeds `B_n` in
`GL_((m+2) n!)(Z)`. ∎

**n = 4.** Forgetting the fourth strand gives `1 -> F_3 -> P_4 -> P_3 -> 1`
(Artin combing; the fiber is the plane minus 3 points). `Delta_4^2` maps to
`Delta_3^2`, and `P_3 / <Delta_3^2> ≅ U_3 ≅ F_2` (the kernel of forgetting the
third strand is free on two generators). The kernel `F_3` meets `<Delta_4^2>`
trivially, since `Delta_4^2` survives the forgetful map. So
`P_4 / <Delta_4^2>` is an extension of `F_2` by `F_3`, which splits because
`F_2` is free.
