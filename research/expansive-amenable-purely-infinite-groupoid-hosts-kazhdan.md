---
rg: 2
id: expansive-amenable-purely-infinite-groupoid-hosts-kazhdan
kind: claim
title: "Some expansive, compactly generated, amenable, minimal, effective, purely infinite ample groupoid has a topological full group containing an infinite hyperbolic Kazhdan group"
distinct_from:
  amenable-purely-infinite-groupoid-full-group-hosts-kazhdan: that host uses Z^3 x| SL_3(Z) on an abstract amenable Cantor model obtained from exactness, which is not a subshift, so it gives no expansive groupoid and depends on the exactness import; this uses a hyperbolic Kazhdan group on its horofunction subshift, so the groupoid is expansive in Nekrashevych's sense and amenability comes from Ozawa's boundary theorem.
  brin-thompson-groups-nv-are-a-t-menable: that asks for the Haagerup property of nV = [[G_2^n]]; this shows that expansivity together with the groupoid properties G_2^n shares with other groupoids does not give it.
  brin-thompson-2v-embeds-in-no-zipper-group: that kills the zipper, local-similarity and wall proofs for nV by distortion; this kills generic groupoid proofs that also use expansivity, by property (T).
---

**OPEN.** The proof is the route `expansive-amenable-purely-infinite-groupoid-kazhdan-host-proof`.
Its mathematics is complete. It requires the narrow OPEN import gap
`hyperbolic-cayley-graph-ozawa-boundary-facts`: thin triangles in Ozawa's sense, and one
in-proof sentence of Ozawa about limits of geodesics.

**Theorem.** Let `Γ` be an infinite word-hyperbolic group with property (T). For example,
take the KMS group `G_HC(1)(p)` with `p ≥ 7` prime, as in
`caprace-kassabov-hyperbolic-kazhdan-alternating-quotients`. There is a second countable,
Hausdorff, ample groupoid `𝒢` on a Cantor set with the following properties.

1. **Expansive.** `𝒢` is compactly generated, and some finite cover of a compact open
   generating set by bisections is expansive in Nekrashevych's sense (arXiv:1511.08241,
   `fullgr.tex` l.825–829): "A finite cover $\mathcal{S}$ of $S$ by bisections is said to
   be expansive if the set $\bigcup_{n\ge 1}(\mathcal{S}\cup\mathcal{S}^{-1})^n$ is a
   basis of topology of $\G$."
2. **Topologically amenable**, in the sense (A) of
   `amenable-purely-infinite-groupoid-kazhdan-host-proof`.
3. Minimal.
4. Essentially principal.
5. Purely infinite in Matui's sense.
6. `Γ ≤ [[𝒢]]`.

**Construction.**

- `Z` is the horofunction subshift of `Γ`: the pointwise limits of the functions
  `b_x = d(x, ·) − d(x, e)` as `x → ∂Γ`, recorded by their increments along the
  generators.
- `F` is a free subshift of `2^Γ` (Gao–Jackson–Seward).
- `M` is a minimal subset of `Z × F`.
- `𝒢 = (M ⋊ Γ) × G_2`.

## Why it matters for nV

- **Expansivity.** The loophole left open in `brin-thompson-groups-nv-are-a-t-menable` was
  "proofs that use compact generation or expansivity of the groupoid". This theorem closes
  it: `G_2^n` is expansive, but so is `𝒢`, and `[[𝒢]]` contains an infinite Kazhdan group.
- **Class-kill.**
  - *Class:* proofs of a-T-menability, or of finiteness of Kazhdan subgroups, for `[[𝒢]]`
    that use only the properties 1–5 of `𝒢`.
  - *Invariant:* property (T) of `Γ`.
  - *Where every member dies:* the passage from 1–5 to a proper cnd function on
    `[[𝒢]]`, whose restriction to `Γ` would be proper on an infinite Kazhdan group. The
    last step needs "(T) plus Haagerup is finite", item 2 of the OPEN gap
    `kazhdan-host-route-imports-have-verbatim-sources`.
- **What separates `G_2^n` from this host.** `G_2^n` carries the continuous cocycle
  `(x, k, y) ↦ k ∈ Z^n`, and its kernel is an AF groupoid. For `𝒢`, the analogous cocycle
  `(h, g) ↦ c(g)` has kernel `(M ⋊ Γ) × AF`, which contains `Γ`. So a proof for `nV` has to
  use the AF-kernel `Z^n` cocycle, the zipper-free product structure, or `nV` itself.
  Whether some other cocycle on `𝒢` has an AF kernel is not addressed.

## Attempts

1. **Horofunction subshift of a hyperbolic Kazhdan group times a free subshift, crossed
   with the full two-shift (2026-09-17, e-nv-affine).** Route
   `expansive-amenable-purely-infinite-groupoid-kazhdan-host-proof`. All steps are written
   out. The only unimported inputs are the two boundary facts of
   `hyperbolic-cayley-graph-ozawa-boundary-facts`.
   - *Dropped variant.* `SL_3(Z[1/p])` acting on the `p`-adic flag variety. `SL_3(Z[1/p])` is
     dense in `SL_3(Q_p)`, not closed, so amenability of `SL_3(Q_p) ↷ SL_3(Q_p)/B` does not
     restrict to it. No amenability proof was found, and the variant was dropped in favour of
     hyperbolic `Γ`.
