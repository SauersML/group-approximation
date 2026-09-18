---
rg: 2
id: product-of-simple-groups-type-a-actions-come-from-factors
kind: claim
title: A type [A_2] action of a product S × T of infinite simple groups forces a factor to have a proper finitely generated subgroup of finite bi-index, or S ≅ T with finitely many conjugacy classes
distinct_from:
  centerless-fp-finitely-many-conjugacy-classes-gives-pbh: that shows finitely many conjugacy classes make the left-right action of G × G on G type (A); this proves the converse classification, that every type [A_2] action of S × T itself comes from that case or from a factor.
  boone-higman-closed-under-finite-direct-products: that is the closure question; this rules out one family of constructions for it, twisted Brin–Thompson envelopes whose actor is the product S × T acting on cosets, and says exactly what such an envelope needs.
  boone-higman-type-a-class-closed-under-finite-extensions: that multiplies type (A) actors of the factors; this shows that, for simple factors, those product actors and the left-right action are the only type [A_2] actions of S × T.
artifacts:
  - research/artifacts/gq-bh-bh-testcases-ranking.md
---

**ESTABLISHED** (lane proof, elementary; not independently reviewed; no priority
claimed).

## Statement

Let `S` and `T` be infinite simple groups and `G = S × T`. Suppose `G` acts faithfully on a
set `Ω` with finitely many orbits on `Ω × Ω` and finitely generated point stabilizers.
These are the orbit and stabilizer conditions of
`twisted-brin-thompson-finite-presentation-criterion`, minus finite presentation. Then at
least one of the following holds.

1. `S` has a proper finitely generated subgroup `H_S` with finitely many double cosets
   `H_S \ S / H_S`.
2. The same holds for `T`.
3. `S ≅ T`, and `T` has only finitely many conjugacy classes.

In cases 1 and 2 the factor already has a faithful type [A_2] coset action. That is the
intrinsic condition of Attempt 8 of `boone-higman-closed-under-finite-direct-products`, and
together with finite presentation it puts that factor in `B_A`. Case 3 is
`centerless-fp-finitely-many-conjugacy-classes-gives-pbh`. By BFFHZ (arXiv:2503.21882v2,
l.376–381, quoted there), it is open whether any infinite finitely presented group has
finitely many conjugacy classes.

## Proof

**Normal subgroups of `G`.** A normal subgroup `N` meets `S × 1` in a normal subgroup of
`S`, so in `1` or `S × 1`.
- If `N ∩ (S × 1) = 1`, then `[N, S × 1] ≤ N ∩ (S × 1) = 1`. So `N` centralizes `S × 1`, and
  `N ≤ Z(S) × T = 1 × T`.
- If `S × 1 ≤ N`, then `N/(S × 1)` is normal in `T`.

So `N ∈ {1, S × 1, 1 × T, G}`. This uses that `S` and `T` are nonabelian, which holds since
they are infinite and simple.

**One orbit.** Let `O = G/H` be an orbit. Finitely many orbits on `O × O` means finitely
many double cosets `H \ G / H`. Let `H_S = p_S(H)` and `H_T = p_T(H)` be the
projections. Both are finitely generated, being images of `H`. The projection
`G → S` maps `H`-double cosets onto `H_S`-double cosets, so `H_S \ S / H_S` is finite, and
likewise for `T`. The kernel of `G` on `O` is `core_G(H)`, one of the four normal
subgroups above.

**Faithfulness forces a good orbit.** The kernels of the orbits intersect in `1`, so some
orbit has kernel `1`, or there are orbits with kernels `1 × T` and `S × 1`.
- **Kernel `1 × T`.** Then `1 × T ≤ H`, so `H = H_S × T`. `H_S ≠ S`, since otherwise
  `H = G` and the kernel would be `G`. So case 1 holds. Kernel `S × 1` gives case 2
  symmetrically.
- **Kernel `1`, a projection proper.** If `H_S ≠ S`, case 1 holds. If `H_T ≠ T`, case 2
  holds.
- **Kernel `1`, both projections onto.** Put `N_S = H ∩ (S × 1)`. It is normal in `H`, so
  `p_S(N_S)` is normalized by `p_S(H) = S`, and `N_S ∈ {1, S × 1}`. If `N_S = S × 1`, then
  `S × 1 ≤ core_G(H) = 1`, which is absurd. So `N_S = 1`, and likewise `N_T = 1`. By
  Goursat's lemma `H = {(s, φ(s)) : s ∈ S}` for an isomorphism `φ : S → T`.

**The graph case.** For `(x, y) ∈ G` put `z = φ(x)^-1 y ∈ T`. For `s, s' ∈ S`,
`φ(s x s')^-1 φ(s) y φ(s') = φ(s')^-1 z φ(s')`. So the `T`-conjugacy class of `z` is an
invariant of the double coset `H (x, y) H`. Conversely, `(x, φ(x) z)` and `(x', φ(x') z)` lie
in one double coset: take `s = x' x^-1`, `s' = 1`. Together with the case `s = 1`, this
shows that double cosets correspond bijectively to conjugacy classes of `T`. So case 3
holds. ∎

## What it rules out

- **Envelopes built on `S × T` itself.** Take a twisted Brin–Thompson or other type (A)
  envelope whose actor is `S × T`, acting on any `G`-set: cosets of `S ⊔ T`, of `S × T`, the
  left-right action on `S`, or a finite union of these. It is finitely presented only
  under case 1, 2 or 3.
  - The route suggested for `boone-higman-closed-under-finite-direct-products` ("S_1 × S_2
    acting on S_1 ⊔ S_2 cosets") therefore gives nothing beyond the intrinsic PBH
    conditions of the factors and the conjugacy-class condition.
  - A product envelope must enlarge the actor beyond `S × T`, which is what FFWZ's
    relative actors do (Attempts 2 and 7 there).
- **More factors.** For `S_1 × … × S_k` the normal subgroups are the sub-products. So
  every orbit is faithful for some sub-product and trivial on the rest. Take a
  stabilizer `H` whose kernel does not contain a given factor.
  - Either some projection `p_i(H)` is proper, and case 1 holds for `S_i`.
  - Or `H` is a subdirect product of the factors it sees, hence a product of diagonal
    subgroups. No diagonal block can be a single factor, since that factor would lie in
    the kernel. So there is a block of size at least 2, and projecting to two of its
    factors gives case 3 for them.
