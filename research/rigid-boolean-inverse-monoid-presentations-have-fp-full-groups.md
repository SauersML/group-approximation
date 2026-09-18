---
rg: 2
id: rigid-boolean-inverse-monoid-presentations-have-fp-full-groups
kind: claim
title: Transfer conjecture for ample groupoids — the V-stabilized full group is finitely presented exactly when the Steinberg algebras are, which makes a rigid groupoid Higman embedding theorem equivalent to the master route
distinct_from:
  v-times-minimal-free-sft-alternating-full-groups-are-fp: that is gate P2 for free minimal SFT crossed products, under finite type alone (which forces rigidity); this is the ring-to-group transfer for every minimal effective ample groupoid, with rigidity made explicit as finite presentation of the Steinberg algebra.
  boolean-inverse-monoid-finite-presentation-is-finite-type: that is the cheap notion (monoid finite presentation), which never sees rigidity; this is the expensive notion Boone–Higman needs.
artifacts:
  - research/artifacts/gq-bh-bh-invent-03-groupoid-higman.md
---

**OPEN** (conjecture of bh-invent-03). The equivalences and implications stated below are lane proofs,
unreviewed.

**Notions.** Let `𝒢` be a minimal effective ample Hausdorff groupoid with Cantor unit space. Write
`A_k(𝒢)` for its Steinberg algebra over a field `k`, `B(𝒢)` for its Boolean inverse monoid of compact
open bisections, and `G_V` for the Cuntz groupoid of Thompson's `V`.
- `𝒢` is *monoid-finitely presented* if `B(𝒢)` is finitely presented.
  - For crossed products `Λ ⋉ X` this is exactly finite type
    (`boolean-inverse-monoid-finite-presentation-is-finite-type`).
  - The notion does not detect rigidity.
- `𝒢` is *rigidly finitely presented over `k`* if, in addition, `A_k(𝒢)` is finitely presented as a
  `k`-algebra.
  - For free SFT crossed products this is quantum rigidity. The Z² case is
    `sft-crossed-product-fp-iff-quantum-rigid`, and the direction "quantum rigid ⇒ fp" over any
    finitely presented `Λ` is `quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products`.

**Conjecture (transfer).** If `𝒢` is rigidly finitely presented over every field, then
`F(G_V × 𝒢) = A(G_V × 𝒢)` is finitely presented. Conversely, if `F(G_V × 𝒢)` is finitely presented,
`𝒢` is rigidly finitely presented over every field.

**What is proved.**
1. **Converse, for free crossed products.** Let `Λ` be finitely presented, `X` free, and `𝒢 = Λ ⋉ X`.
   - If `F(G_V × 𝒢)` is finitely presented, then `X` is an SFT that is quantum rigid over every field
     (`fp-v-times-subshift-full-groups-force-quantum-rigidity`).
   - So `A_k(𝒢)` is finitely presented for every `k`
     (`quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products`), and `B(𝒢)` is finitely presented
     (`boolean-inverse-monoid-finite-presentation-is-finite-type`).
2. **The monoid notion is strictly weaker than the group one.**
   `fp-boolean-inverse-monoids-need-not-have-fp-full-groups` gives free SFT crossed products that are
   monoid-finitely presented but have non-finitely-presented `F(G_V × 𝒢)`.
3. **Known instances of the forward direction.** Each has finitely presented Steinberg algebra and
   finitely presented full group.
   - `𝒢` a point, where the full group is `V`.
   - One-sided SFT and Cuntz–Krieger groupoids: Matui for the full group, Leavitt path algebras for the
     ring.
   - The deterministic Li-coded groupoids of `finitely-coded-cantor-actions-give-type-a-hosts`, where
     unique factorization forces the range idempotents to commute. For those the ring statement is
     plausible but not checked here.
4. **Forward direction on free minimal SFT crossed products.** On this class the forward direction is
   exactly master-route gate P2 (`v-times-minimal-free-sft-alternating-full-groups-are-fp`), with its
   hidden rigidity hypothesis made explicit.

**Groupoid Higman embedding (GHE), rigid form.** Every effective ample groupoid `𝒢_0` whose Boolean
inverse monoid is computably presented, and which is free on a dense set, is a clopen restriction of a
minimal ample groupoid `ℋ` that is rigidly finitely presented over `F_2`. An open subgroupoid over a
clopen of `ℋ⁰` is enough, since only `F(𝒢_0) ↪ F(ℋ)` is used.

**GHE plus transfer implies Boone–Higman** (lane proof).
- Let `G` be finitely generated with solvable word problem, and let `X_G ⊆ {0,1}^G` be an effectively
  closed free subshift (an effective Gao–Jackson–Seward subshift). Then `𝒢_0 = G ⋉ X_G` is as above.
- GHE gives `ℋ`. Then `G ≤ F(𝒢_0) ≤ F(ℋ) ≤ F(G_V × ℋ)`: extend by the identity off the clopen, and
  multiply by `1_C`.
- The transfer conjecture makes `F(G_V × ℋ)` finitely presented. It is simple, because it equals
  `A(G_V × ℋ)`, which is simple by Nekrashevych for minimal `ℋ`.

**Where the two halves sit on the master route.**
- **Plain GHE.** The monoid-finitely-presented (non-rigid) form of GHE, for group inputs, is gate P1
  (`decidable-groups-embed-in-fp-groups-with-minimal-free-sft`), minus minimality. Put the input in a
  finitely presented `Λ₀` with solvable word problem (Clapham), then take a free SFT on `Λ₀ × Z²`.
  Free SFTs on `Λ₀ × Z²` are expected from the Barbieri–Sablik simulation theorem; that source was not
  re-read.
- **Rigidity.** It is gate G2, and the transfer conjecture is gate P2.

**The embedding must be an embedding, not a quotient** (lane proof, recorded in the artifact).
- **The quotient.** Simulating `G`'s free subshift over a presentation cover `F_k → G`, instead of over
  a finitely presented overgroup `Λ₀ ⊇ G`, gives only a groupoid *quotient*: the `F_k`-germs upstairs
  are finer than the `G`-germs downstairs. So full groups lift only non-homomorphically, and the lifted
  generators generate `F_k`, not `G`.
- **Cocycle lifting.** Full groups of free actions are functorial along equivariant extensions: an
  equivariant surjection `Y -> X` with `Λ ↷ X` free gives an injective homomorphism
  `F(Λ ⋉ X) ↪ F(Λ × H ⋉ Y)`, sending a cocycle `c` to `c ∘ π`.
- **Consequence.** GHE for groups needs the input's relations to hold in the acting group. That is why
  Clapham's theorem is unavoidable on every symbolic route, and why decidability enters (Jeandel).

**Lesson for general BH.**
- The groupoid-level question has a clean shape: *Higman embedding* holds cheaply in the monoid category
  (it is gate P1).
- All of Boone–Higman's difficulty is concentrated in one categorical step, the passage from a Boolean
  inverse monoid to its group of units. That step must be paid for by *rigidity*, i.e. finite
  presentation of the Steinberg algebra.
- So the transfer conjecture is the group-theoretic core of the master route, stated for all ample
  groupoids. A proof for any class of rigid groupoids beyond the deterministic Li-coded ones, starting
  with Labbé's Z² shift, would be the first finite-presentation certificate for non-deterministic
  full groups.
