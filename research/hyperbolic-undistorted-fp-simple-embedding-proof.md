---
rg: 2
id: hyperbolic-undistorted-fp-simple-embedding-proof
kind: route
title: Check that each step G <= G*Z <= [[G*Z | horofunction boundary]] <= SV_Gamma of the BBMZ chain is undistorted, using free-factor retraction and full-group label length
target: hyperbolic-groups-undistortedly-embed-in-fp-simple-groups
requires:
  - full-group-label-length-bounds-distortion
  - g-free-z-acts-locally-faithfully-on-horofunction-boundary
  - hyperbolic-groups-embed-in-contracting-rsgs
  - contracting-rsgs-embed-in-fp-simple-groups
---

Lane proof, not independently reviewed. The BBMZ statements are read at source, arXiv:2309.06224v3 TeX
(copy at `$GQ/src/bh-free-03/bbmz2-2309.06224.tex`).

**Imports (BBMZ).**
- (B1) `thrm:hyp_to_contracting` with its proof. For nontrivial hyperbolic `G`, `G' = G*Z` is hyperbolic,
  acts faithfully on `∂_h G'` (`thrm:FreeProductBoundary`), and `Γ := [[G' | ∂_h G']]` is a full contracting
  RSG containing `G'`.
- (B2) `thrm:fin_pres`: full contracting RSGs are finitely presented. So `Γ` is finitely generated.
- (B3) `prop:contr_to_simple` with its proof. `Γ` acts faithfully on the orbit `S` of a rational point,
  since `S` is dense. `SV_Γ = [[V ≀_S Γ | C^S]]` is finitely presented (`thrm:action_to_simple`, citing
  Zaremsky arXiv:2201.00711 Thm 4.2) and simple, and `Γ` embeds in `SV_Γ` as coordinate permutations.
- (B4) `def:full`: full groups on compact spaces consist of maps agreeing with group elements on the
  members of a finite open cover.

**Step 1. `G <= G'` is undistorted.** Use the generating set `S_G ∪ {t}`. The retraction `G' -> G` killing
`t` is a homomorphism that is the identity on `G` and does not increase word length, so
`|g|_G <= |g|_{G'}`.

**Step 2. `G' <= Γ` is undistorted.** By `g-free-z-acts-locally-faithfully-on-horofunction-boundary`, no
nontrivial element of `G'` fixes a nonempty open subset of `∂_h G'` pointwise. `∂_h G'` is compact, `Γ`
is finitely generated (B2), and `G' <= Γ <= [[G' | ∂_h G']]`. So the plain form of
`full-group-label-length-bounds-distortion` gives `|g|_{G'} <= C |g|_Γ`.

**Step 3. `Γ <= SV_Γ` is undistorted.** `Γ` acts faithfully on `S` (B3), and `SV_Γ` is finitely generated
(B3). So the twisted Brin–Thompson form of `full-group-label-length-bounds-distortion` gives
`|γ|_Γ <= C' |γ|_{SV_Γ}`. This is item 2 of the target for an arbitrary full contracting RSG. For `K = SV_Γ` it is Belk–Zaremsky,
arXiv:2001.04579, Theorem 1.2, which gives a quasi-retraction; either proof suffices.

**Conclusion.** Composing the three steps, `|g|_G <= C'' |g|_{SV_Γ}` for `g ∈ G`. The reverse inequality
`|g|_{SV_Γ} <= C''' |g|_G` holds for any homomorphism between finitely generated groups. So
`G -> SV_Γ` is a quasi-isometric embedding into a finitely presented simple group. ∎

**Calibration.**
- The argument does not prove too much: it never uses the RSG structure beyond finite generation, and
  the plain form needs local faithfulness. Example: for the Grigorchuk group acting on
  the binary tree, `b` fixes the cone `110·` pointwise, so the plain form does not apply to
  Röver–Nekrashevych hosts of such groups.
- Local faithfulness is essential in the plain form, and full groups themselves never have it: `V` contains
  elements supported on a single cone. That is why the lemma is applied to the group `G*Z`, not to `Γ`. The
  twisted Brin–Thompson form instead uses the coordinate-permutation label, which is locally determined even
  though `V ≀_S Γ` is not locally faithful.
