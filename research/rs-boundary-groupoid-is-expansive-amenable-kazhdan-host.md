---
rg: 2
id: rs-boundary-groupoid-is-expansive-amenable-kazhdan-host
kind: claim
title: "The Robertson–Steger boundary action of a Kazhdan PGL_3 lattice is an amenable, minimal, expansive subshift on a Cantor set; its action groupoid (and its product with G_2) is compactly generated and expansive with an infinite Kazhdan group in its full group, so compact generation and expansivity do not separate G_2^n from Kazhdan hosts"
distinct_from:
  rank-two-prefix-replacement-groups-contain-infinite-kazhdan: that proves the lattice acts by rank-two prefix replacements, faithfully and without invariant measures; this adds the groupoid-level properties (Cantor space, expansive action, minimality, amenability, compact generation, expansivity of the groupoid and of its product with G_2), which extend the class kill to proofs that use compact generation or expansivity.
  amenable-purely-infinite-groupoid-full-group-hosts-kazhdan: that host (M ⋊ Γ) × G_2 is free (effective) but open on citations and not known to be expansive; this host is expansive and established, but its effectiveness is not asserted.
  input-encoded-sft-groupoid-hosts-are-not-universal: that shows rank-one SFT groupoids contain no infinite Kazhdan group; this shows that expansivity, the property those groupoids share with G_2^n, does not suffice.
---

**ESTABLISHED** through `rs-boundary-groupoid-is-expansive-amenable-kazhdan-host-proof`.

## Setting

As in `rank-two-prefix-replacement-groups-contain-infinite-kazhdan`:
- `K` is a nonarchimedean local field of characteristic zero, and `B` is the building of
  `PGL_3(K)`, with boundary `Ω`.
- `Γ` is a lattice acting type rotatingly, freely on vertices, with finitely many vertex
  orbits.
- `R = Γ × Ω` is the action groupoid, with Nekrashevych's convention
  (`nekrashevych-expansive-groupoid-criteria`).
- `[[𝒢]]` is the group of bisections `F` with `s(F) = r(F) = 𝒢^{(0)}`.

## Statement

1. `Γ` is infinite, finitely generated and has property (T), and `Ω` is a Cantor set.
2. **Expansive.** The action `Γ ↷ Ω` is expansive: there is a neighbourhood `W` of the
   diagonal such that `(gx, gy) ∈ W` for all `g ∈ Γ` forces `x = y`. Hence `Γ ↷ Ω` is a
   subshift, and both `R` and the groupoid of germs of the action are compactly generated
   and expansive.
3. **Minimal.** Every `Γ`-orbit in `Ω` is dense.
4. **Amenable.** `Γ ↷ Ω` is amenable in the sense of Anantharaman-Delaroche, Definition 2.1.
   `C(Ω) ⋊ Γ = C(Ω) ⋊_r Γ` is simple, nuclear and purely infinite.
5. **No invariant measure.** `Ω` carries no `Γ`-invariant Borel probability measure, and
   every orbit is infinite.
6. **Kazhdan group in the full group.** `g ↦ {g} × Ω` is an injective homomorphism
   `Γ → [[R]]`. Since the action is faithful, `Γ` also embeds in the full group of the
   germ groupoid, which is effective and minimal.
7. **Product with G_2.** `R × G_2` is compactly generated, expansive and minimal, and
   `g ↦ ({g} × Ω) × G_2^{(0)}` embeds `Γ` in `[[R × G_2]]`.

**Not asserted.**
- That `Γ ↷ Ω` is topologically free, i.e. that `R` is effective.
- That the germ groupoid is amenable.
- That `R` is purely infinite in Matui's groupoid sense.

## Consequence (class kill, calibration of nV)

**Killed class.** Proofs that `[[𝒢]]` has the Haagerup property, or that its Kazhdan
subgroups are finite, from any of the following hypothesis lists:
- **(L_R)** `𝒢` is étale with Cantor unit space, compactly generated, expansive and
  minimal; it is the groupoid of an amenable action of a finitely generated group; it has
  infinite orbits and no invariant probability measure; its C\*-algebra is simple, nuclear
  and purely infinite. Optionally `× G_2`.
- **(L_germ)** `𝒢` is étale with Cantor unit space, compactly generated, expansive,
  minimal and effective, with no invariant probability measure.

**Invariant:** property (T) of `Γ`.

**Where every member dies:** at the step producing a proper conditionally negative
definite function `ψ` on `[[𝒢]]`, or a finiteness conclusion, applied to `R`, to `R × G_2`,
or to the germ groupoid. Restricted to the infinite Kazhdan subgroup `Γ`, `ψ` is bounded
(Delorme–Guichardet, BdlHV Theorem 2.12.4), so it is not proper. Finiteness fails because
`Γ` is infinite.

**What survives.**
- At the groupoid level, only proofs using effectiveness and amenability *together with*
  expansivity. The effective amenable host `amenable-purely-infinite-groupoid-full-group-hosts-kazhdan`
  is not known to be expansive, and this host is not known to be effective.
- At the word-system level, the product factorization of `G_2^n`
  (`rank-two-prefix-replacement-groups-contain-infinite-kazhdan`).
- Compact generation and expansivity cannot be the distinguishing hypotheses of a Haagerup
  proof for `2V`.
