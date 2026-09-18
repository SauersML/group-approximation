---
rg: 2
id: rs-boundary-groupoid-is-expansive-amenable-kazhdan-host
kind: claim
title: "The Robertson–Steger boundary action of a Kazhdan PGL_3 lattice is an amenable, minimal, expansive subshift on a Cantor set; its action groupoid (and its product with G_2) is compactly generated and expansive with an infinite Kazhdan group in its full group, so compact generation and expansivity do not separate G_2^n from Kazhdan hosts"
distinct_from:
  rank-two-prefix-replacement-groups-contain-infinite-kazhdan: that proves the lattice acts by rank-two prefix replacements, faithfully and without invariant measures; this adds the groupoid-level properties (Cantor space, expansive action, minimality, amenability, compact generation, expansivity of the groupoid and of its product with G_2), which extend the class kill to proofs that use compact generation or expansivity.
  amenable-purely-infinite-groupoid-full-group-hosts-kazhdan: that host (M ⋊ Γ) × G_2 is free (effective) but open on citations and not known to be expansive; this host is expansive and established, but its effectiveness is not asserted.
  input-encoded-sft-groupoid-hosts-are-not-universal: that shows rank-one SFT groupoids contain no infinite Kazhdan group; this shows that expansivity, the property those groupoids share with G_2^n, does not suffice.
artifacts:
  - research/artifacts/nv2-expansivity-calibration-audit-2026-09-18.md
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
- **Hausdorffness is a second escape, not covered by the word "only" above.** See the
  audit below, D1.

## Attempts

- **Adversarial audit, 2026-09-18 (`e2-w2-audit-nv2`, wave `swarm-0917`). Verdict:
  survives.** Full record in
  `research/artifacts/nv2-expansivity-calibration-audit-2026-09-18.md`. The five claims
  that landed on 2026-09-17 without a referee — this one,
  `ample-groupoid-products-expansive-iff-factors-are`,
  `nekrashevych-expansive-groupoid-criteria`,
  `ad-nuclear-crossed-product-gives-amenable-action` and
  `robertson-steger-word-products-and-boundary-topology` — were re-checked against
  independently re-downloaded TeX sources (arXiv:1511.08241, arXiv:math/0005014,
  arXiv:1302.5593). Every imported sentence matches character by character, with the same
  standing hypotheses. All five keep ESTABLISHED.
  - **Citation lens.** Nekrashevych's reading of "expansive groupoid" adopted by the import
    node is confirmed, not merely consistent: Theorem `th:universalcov` ("A compactly
    generated groupoid `𝒢` is expansive if and only if there exists a finite generating set
    `𝒮` of bisections such that …") presupposes exactly it. Anantharaman-Delaroche
    Theorem 3.4's hypotheses (`X` locally compact, `G` locally compact, discrete for
    (4) ⇒ (1)) are the ones used. Robertson–Steger's (H0)-(H3) are in force for a
    `PGL_3(K)` lattice, `K` nonarchimedean of characteristic zero.
  - **Proof-gap lens.** Every step of both non-transcription proofs was re-derived. No step
    is wrong. The checks that could have failed and did not are listed in §2 of the audit;
    in particular the openness of the refined generating set in the product proof's
    "only if" direction, the fixed second coordinate `z` in its projection step, and here
    the undecorated restriction in Lemma A(e) and the strict-refinement argument behind
    the minimal shape `m` in Step 2.
  - **D1 (material, recorded, not refuting).** "What survives … **only** proofs using
    effectiveness and amenability together with expansivity" overstates. `R` is Hausdorff
    but is not known to be effective; the germ groupoid is effective but is not known to be
    Hausdorff. So a Haagerup proof from **{Hausdorff, étale, Cantor unit space, compactly
    generated, expansive, minimal, effective, no invariant probability measure}** — the
    list `G_2^n` actually satisfies, and the setting of every recorded theorem in this area
    including Matui's — is refuted by neither host. `(L_germ)` as written omits
    Hausdorffness, so the claim is true as stated; the kill simply does not reach the
    standard framework.
  - **What closes D1.** Topological freeness of `Γ ↷ Ω` (that
    `int{ω : γω = ω} = ∅` for every `γ ≠ 1`). It would give `R = germ groupoid`, hence one
    groupoid with every listed property of `G_2^n` except the product factorization, hosting
    an infinite Kazhdan group. Two routes and their first falsifiable steps are in §3.1 of
    the audit: an internal Robertson–Steger route that reduces to the shape equality
    `σ(ū) = σ(v̄)` (which should follow from thickness making
    `m ↦ #{w ∈ W_m : o(w) = a}` strictly increasing), and a flag-variety route that needs
    the `Γ`-equivariant identification of `Ω` with `G/B(K)`, an import the graph lacks.
  - **D2 (free strengthening).** Nekrashevych's Proposition `pr:essprincipalHaus` also says
    "Every second countable groupoid of germs is essentially principal", and its proof does
    not use Hausdorffness of the groupoid. The germ groupoid here is second countable, so it
    is **essentially principal** at no cost, and that property — one of the five that
    `brin-thompson-groups-nv-are-a-t-menable` lists for `G_2^n` — can be added to
    `(L_germ)`. This isolates Hausdorffness as the only remaining structural escape at the
    effective end, alongside amenability and Matui pure infiniteness of the germ groupoid.
  - **D3 (implicit step, filled).** `robertson-steger-word-products-and-boundary-topology`
    derives "`D` is finite" from "`A` is finite", but Robertson–Steger only fix `A` finite
    as a Section 1 convention and then *redefine* `A = Γ\𝔗` in Section 7 without proving
    that quotient finite. It is finite, because `ℬ` is locally finite and `Γ` has finitely
    many vertex orbits. The step is load-bearing: `D` finite makes `𝒜` unital
    (Remark `finitedecorate`), which is what lets Remark `previous` — and hence the Remark
    after `main2`, the source of simplicity, nuclearity and pure infiniteness — apply.
