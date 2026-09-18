---
rg: 2
id: renormalization-heights-force-eigenvalue-roots
kind: claim
title: A height-m renormalization makes the eigenvalue group closed under m-th roots, and a coprime renormalization multiplies each p-adic clock by the inverse height
distinct_from:
  renormalizable-thompson-elements-are-odometer-codes: that shows one height-m renormalization gives a factor onto Z_m; this constrains a base that carries renormalizations of several heights at once.
  renormalizable-thompson-elements-give-baumslag-solitar: that turns one renormalization into BS(1,m); this is the obstruction theory for combining renormalizations of coprime heights, as Aff(Q) requires.
  aff-q-embeds-in-fp-simple-group: that is the stepping-stone target; this states what a single renormalizable base for all prime dilations would have to satisfy.
artifacts:
  - research/artifacts/gq-affq-coprime-renormalization-test.md
---

**ESTABLISHED** through `renormalization-heights-force-eigenvalue-roots-proof`. Elementary lane
proof, not independently reviewed. No priority claimed: both items are standard tower arguments.

**Setting.** `T` is a homeomorphism of a compact metric space `X`. A **height-`m`
renormalization** is a pair `(A, φ)`:
- `A` is clopen, `X = A ⊔ TA ⊔ … ⊔ T^{m-1}A`, and `T^m A = A`;
- `φ: A -> X` is a homeomorphism with `φ ∘ T^m|_A = T ∘ φ`.

This is the definition of `renormalizable-thompson-elements-give-baumslag-solitar` without the
brick-local clause. `E(T) ⊆ S^1` is the group of continuous eigenvalues: the `μ` for which some
continuous `f: X -> S^1` has `f ∘ T = μ f`.

**Statement.**
1. **Roots.** If `T` has a height-`m` renormalization, then `E(T) = {μ ∈ S^1 : μ^m ∈ E(T)}`.
   So `E(T)` contains every `m^j`-th root of unity and is closed under `m`-th roots.
2. **Several heights.** If `T` has height-`m` renormalizations for every `m` in a set `M`, then
   `E(T)` is closed under `m`-th roots for every `m ∈ M`. If `M` contains every prime, `E(T)`
   contains every root of unity. If `T` is also minimal, it factors onto the universal
   odometer `Ẑ`.
3. **Clock action.** Let `T` be minimal, let `(A_q, φ_q)` be a height-`q` renormalization, and let
   `π: X -> G` be continuous, where `G` is a compact abelian group, with `π ∘ T = π + g`.
   Suppose `G` is uniquely `q`-divisible; for example `G = Z_p` with `p ∤ q`. Then there is a
   constant `c ∈ G` with
   `π ∘ φ_q = q^{-1} π + c` on `A_q`.
   So a height-`q` renormalization acts on every `p`-adic clock (`p ∤ q`) by the affine map
   `x ↦ q^{-1} x + c`. This is a unit multiplication, not a digit shift.

**Consequences for the `Aff(Q)` route.**
- `aff-q-embeds-in-fp-simple-group` through `nV` needs, inside one group, an `s` conjugate to
  `s^p` for every prime `p`. Suppose this is obtained, as in
  `renormalizable-thompson-elements-give-baumslag-solitar`, from one base `T` carrying
  renormalizations of every prime height. If `T` is minimal, as SMART-type bases are, then item 2
  forces a factor of `T` onto `Ẑ`.
- By item 3, the renormalization for each prime `q` must act on the `p`-adic clock of every other
  prime `p` by the unit multiplication `x ↦ q^{-1}x + c`. In base-`p` digits that map has
  unbounded carries.
- For SMART's induced map `U` only a factor onto `Z/2 × Z_3` is known
  (`smart-level-zero-return-map-factors-onto-3-adic-odometer`). If `Z/2 × Z_3` is its maximal
  equicontinuous factor, then item 1 excludes every height `m` with a prime factor `≠ 3`. For
  `m = 2` the reason is that `i ∉ E(U)`; for `m = 5`, that there is no primitive fifth root of
  unity. So `U` would be a base for powers of `3` only. Maximality of that factor is not
  established.
