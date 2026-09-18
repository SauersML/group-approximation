---
rg: 2
id: baumslag-gersten-group-is-hughes-free-embeddable
kind: claim
title: The Baumslag-Gersten group, a non-residually-finite one-relator group of primitivity rank 2, has Hughes-free division rings over every division ring, so its Lewin-Lewin ring is Hughes-free in characteristic p
distinct_from:
  vertex-injective-quotients-give-hughes-free-division-rings: that is the general closure theorem; this applies its retract-HNN case to the primitivity-rank-2 one-relator groups that FSP leave open in positive characteristic, checks that the examples lie outside every previously covered class, and records the Magnus-hierarchy form of the criterion.
  nonsofic-one-relator-relator-has-primitivity-rank-two: that shows a non-residually-finite one-relator group has primitivity rank 2; this uses that case analysis to place Baumslag-Gersten in the open case, and settles division-ring embedding there.
  higman-bs-amalgam-has-hughes-free-division-rings: that treats BS(1,2) amalgams inside Higman's group; this treats the HNN extension of BS(1,2) along its two cyclic Magnus subgroups, which is one-relator and locally indicable.
  kaplansky-zero-divisor-conjecture: that is the conjecture; this is a new positive-characteristic instance of its embedding form, for a group outside the residually finite, amenable, residually torsion-free nilpotent, free-by-cyclic and 3-manifold classes.
---

**ESTABLISHED** (new class) by [[baumslag-gersten-group-is-hughes-free-embeddable-proof]].

Let `BG = <a, t | (a^t)^{-1} a (a^t) = a^2>`, where `a^t = t^{-1} a t`. More generally, let
`G(1,n) = <a, t | (a^t)^{-1} a (a^t) = a^n>` for `n ≠ 0`. Let `𝓗` be the class of hereditarily Hughes-free
embeddable groups of [[vertex-injective-quotients-give-hughes-free-division-rings]]. Every division ring and every
characteristic is allowed.

**Theorem.**
1. **Membership.** `G(1,n) ∈ 𝓗` for every `n ≠ 0`. So every crossed product `E * G(1,n)` over a division ring
   has a Hughes-free division ring. In particular `k[BG]` embeds in `D_{kBG}` for every field `k`, of any
   characteristic.
2. **Lewin–Lewin and q:HF.** For every division ring `k`:
   - the Lewin–Lewin division ring of `k[G(1,n)]` is Hughes-free (FSP Question 7.13 has a positive answer for
     these groups);
   - FSP's graph-of-rings embedding is Hughes-free for every splitting of `G(1,n)` (q:HF);
   - the compatibility statement of [[fsp-q-hf-reduces-to-hyperbolic-kernel-pairs]] holds for all of its
     pairs, hyperbolic kernels included.
3. **`BG` is in the open case.**
   - `BG` is torsion-free, one-relator and locally indicable.
   - It is not residually finite: `a` dies in every finite quotient.
   - Its relator has primitivity rank exactly 2.
   - The kernel `N` of `BG -> Z` is perfect, so every solvable quotient of `BG` is cyclic.
   - `BG` contains `F_2`, so it is not amenable.
   - No finite-index subgroup of `BG` is free-by-cyclic, in any rank.
   - `BG` is not residually torsion-free nilpotent.

   Hence `BG` is not virtually compact special, not a 3-manifold group, not virtually free-by-cyclic, not
   amenable and not residually torsion-free nilpotent. So none of FSP (VCS), Jaikin-Zapirain (amenable, RTFN,
   free-by-cyclic), Sánchez-Peralta (3-manifolds) or JKSP (virtually free-by-cyclic) covers it.
4. **A version that is not bi-orderable.** Let `Kl = <x, y | y^{-1} x y = x^{-1}>` be the Klein bottle group, and
   `G_Kl = (BS(1,2) × Kl) *_θ` with `θ: a ↦ b` (so `t^{-1} a t = b`). Then `G_Kl ∈ 𝓗`. It contains `BG` and
   `Kl`, so it is not residually finite and not bi-orderable, and Malcev–Neumann series do not apply to it. The
   same holds for the free product `BG * Kl`, which is two-relator.
5. **Retractive Magnus hierarchies.** Let `G = <X | w>` be torsion-free one-relator, with `t ∈ X` of exponent
   sum zero. Magnus–Moldavanskii rewriting gives `G = B *_θ`, where `B` is one-relator of lower complexity and
   `A, C = θ(A)` are Magnus subgroups. If `B ∈ 𝓗` and `B` retracts onto `A` or onto `C`, then `G ∈ 𝓗`.

   A retraction `B -> C` exists exactly when substituting words in the free generators of `C` for the remaining
   generators makes the rewritten relator trivial in the free group `F(C)`. For `BG`, `B = BS(1,2)` and the
   substitution `a ↦ 1` works. Iterating over the hierarchy (free groups at the bottom, with free products
   handled by closure under free products) gives a recursively checkable sufficient condition for a one-relator
   group to lie in `𝓗`, in every characteristic.

**Honest scope.**
- Whether `BG` itself is bi-orderable is not settled here. I found no statement either way. If it were, the
  existence of `D_{kBG}` would already follow from Malcev–Neumann. Item 4 gives examples that avoid this caveat.
- This settles FSP's open positive-characteristic case (Question 7.13) only for one-relator groups with a
  retractive Magnus hierarchy, not for all groups of primitivity rank 2.
- Kaplansky's zero-divisor conjecture for `k[BG]` was already known, since torsion-free one-relator groups are
  locally indicable. What is new is the embedding into a (Hughes-free) division ring in characteristic `p`.
