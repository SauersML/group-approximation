---
rg: 2
id: thompson-f-co-amenable-circle-hosts-reduce-to-line-hosts
kind: claim
title: Under every embedding, a circle group containing F co-amenably preserves a probability measure, is not minimal, and reduces to a line host or a gap host
distinct_from:
  thompson-f-is-not-co-amenable-in-its-known-nonamenable-hosts: that fixes the standard action of F on the circle and uses its fixed point; this allows every embedding of F (or of any group without free subgroups) into Homeo(S^1) and every non-amenability witness of the host, free subgroups included.
  margulis-circle-weak-tits-alternative: that is the imported alternative for a single circle group; this pushes its measure from a co-amenable subgroup up to the host and reads off the host's structure.
  thompson-t-orbits-carry-no-invariant-means: that is about invariant means on T-orbits of points; this is about coset spaces of copies of F in arbitrary circle groups.
  amenable-infinite-simple-circle-groups-fix-a-point: that starts from an amenable acting group; here the host is non-amenable and only a co-amenable subgroup lacks free subgroups.
artifacts:
  - research/margulis-circle-weak-tits-alternative.md
---

**ESTABLISHED.** Let `H` be a group with no non-abelian free subgroup. Let
`H ≤ G ≤ Homeo(S^1)` be any embedding. The action of `H` need not be the standard one, and
nothing is assumed about how the non-amenability of `G` is witnessed. Suppose `H` is
co-amenable in `G`. Write `G^+ = G ∩ Homeo_+(S^1)`. Then:

1. **Measure.** `G` preserves a Borel probability measure `μ` on `S^1`.
2. **Rotation part.** `ρ(g) = μ([x, gx)) mod 1` is a homomorphism `G^+ → R/Z` that does not
   depend on `x`. Its kernel `K` fixes `supp μ` pointwise, so `[G^+, G^+] ≤ K`.
3. **Full support forces abelian.** If `supp μ = S^1`, then `G^+` is abelian, so `H` has an
   abelian subgroup of index at most 2. This holds in particular when `G` acts minimally.
4. **Atoms give a line host.** Suppose `μ` has an atom and `G` is non-amenable.
   - `G` has a finite orbit `O`. The subgroup `G_1 ≤ G^+` fixing `O` pointwise is normal and
     of finite index in `G`.
   - For some component `J` of `S^1 \ O`, an open interval, the image `Q` of `G_1` in
     `Homeo_+(J) ≅ Homeo_+(R)` is non-amenable.
   - The image of `H ∩ G_1` is co-amenable in `Q`. It is a quotient of a finite-index subgroup
     of `H`.
5. **Atomless, not full: a gap host.** Suppose `μ` has no atom and `supp μ ≠ S^1`.
   - `G^+` permutes the countably many components ("gaps") of `S^1 \ supp μ`, and every gap
     has stabilizer exactly `K`.
   - `K` embeds in `∏_{gaps J} Homeo_+(J)`.
   - `H ∩ K` is co-amenable in `G^+`, and `K` is non-amenable whenever `G` is.

**For Thompson's group `F`** (no free subgroups: `thompson-f-has-no-free-subgroups`):
- No finite-index subgroup of `F` is abelian. So case 3 never happens: **a minimal group of
  circle homeomorphisms contains no copy of `F` co-amenably.** This holds for `T` under every
  embedding `F ↪ T`, not only the standard one, and for every minimal overgroup of `F`,
  whatever witnesses its non-amenability.
- In case 4 the line host `Q` contains a faithful copy of the simple group `F' = [F,F]`
  co-amenably. Non-amenability of `F'` is equivalent to that of `F`.
- The heretic's circle case (`thompson-f-is-not-co-amenable-in-its-known-nonamenable-hosts`,
  case 1) is the special case of the standard embedding. There the only `F`-invariant
  probability is `δ_0`, so `μ = δ_0` and `G` fixes `0`.

**The invariant, and where every member dies.** The invariant is the Margulis measure: `H`
has no free subgroup, so it preserves a probability on `S^1`
(`margulis-circle-weak-tits-alternative`). Every co-amenable circle host dies at Eymard's
transfer, which lifts that measure to the host. The host's rotation homomorphism then
leaves only interval dynamics, on the complement of a finite orbit (case 4) or on the gaps of
a Cantor support (case 5).

**Survivors.** After this claim the host route for `F` has only these one-dimensional
survivors:
- **Line hosts:** `F'`, embedded arbitrarily, co-amenable in a non-amenable `Q ≤ Homeo_+(R)`.
  The heretic's measured kills cover only the Thurston embedding.
- **Gap hosts:** case 5, where co-amenability of `H ∩ K` in `G^+` does not descend to `K`
  (Monod–Popa).
- **Non-circle hosts:** Cantor hosts such as `nV`, and hosts with no action on a
  one-manifold.

Proof route: `thompson-f-co-amenable-circle-hosts-reduce-to-line-hosts-proof`.
