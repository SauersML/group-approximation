---
rg: 2
id: baumslag-gersten-neither-linear-nor-self-similar-proof
kind: route
title: The order of the image of a divides 2^n - 1 for its own order n, which forces n = 1; then Malcev and level stabilizers finish
target: baumslag-gersten-group-is-neither-linear-nor-self-similar
requires: []
artifacts:
  - research/artifacts/bh-baumslag-gersten-2026-09-12.md
---

**Item 1.** Let `π: BG -> F` with `F` finite, and put `n = ord(π a)`.
- `π b = π t · π a · (π t)^-1`, so `ord(π b) = n`.
- Iterating `π b · π a · (π b)^-1 = (π a)^2` gives
  `(π b)^k π a (π b)^-k = (π a)^(2^k)`. At `k = n` this reads
  `π a = (π a)^(2^n)`, so `n | 2^n - 1`. In particular `n` is odd.
- Suppose `n > 1`, and let `p` be the least prime factor of `n`. Then
  `2^n ≡ 1 (mod p)`, and `2^(p-1) ≡ 1 (mod p)` by Fermat. So `ord_p(2)` divides
  `gcd(n, p-1)`.
- Every prime factor of `n` is at least `p`, and every prime factor of `p - 1`
  is below `p`, so `gcd(n, p-1) = 1`. That gives `2 ≡ 1 (mod p)`, which is
  impossible.
- Hence `n = 1` and `π a = 1`.
- `<<a>>` contains `b = t a t^-1`, and `BG / <<a>> = < t > ≅ Z`. So every finite
  image is a quotient of `Z`, hence cyclic.

**Item 2.** `BG` is the HNN extension of `B = <a_0, a_1 | a_1 a_0 a_1^-1 = a_0^2>`
along `a_0 -> a_1` (the Magnus rewriting recorded in
`baumslag-gersten-base-is-elliptic-in-every-tree-action`). Base groups embed in
HNN extensions, and `a_0 ≠ 1` in `B = BS(1,2)`, so `a ≠ 1` in `BG`. By item 1, `a`
lies in the kernel of every map to a finite group. So `BG` is not residually
finite.

**Item 3.** Malcev: every finitely generated subgroup of `GL_m(K)`, for a
field `K`, is residually finite. `BG` is finitely generated and not residually
finite, so it embeds in no `GL_m(K)`.

**Item 4.** Let `T` be a locally finite rooted tree. The pointwise stabilizer
`St(ℓ)` of level `ℓ` is normal of finite index in `Aut(T)`, and the
intersection over `ℓ` of `St(ℓ)` is trivial. So `Aut(T)` and all its subgroups
are residually finite. `BG` therefore embeds in no `Aut(T)`, and in particular in
no self-similar group `H ≤ Aut(T_d)`. ∎
