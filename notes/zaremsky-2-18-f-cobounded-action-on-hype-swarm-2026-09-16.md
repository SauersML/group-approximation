# Zaremsky 2.18 (F acting coboundedly on H^2): swarm lane notes, 2026-09-16

Target: `zaremsky-2-18-f-cobounded-action-on-hyperbolic-plane`.
Hole locked and worked: `thompson-f-has-no-cobounded-action-on-spaces-qi-to-h2`.

## Setup on arrival

- `zaremsky-2-18-by-no` requires two claims:
  - `thompson-f-has-no-cobounded-action-on-hyperbolic-plane`, about isometries of `H^2` itself;
  - `thompson-f-has-no-cobounded-action-on-spaces-qi-to-h2`, the source reading "(a space
    quasi-isometric to) the hyperbolic plane" of arXiv:2406.12982, Question 11.4.
- The QI claim had one route, `thompson-f-no-cobounded-qi-h2-action-via-markovic`. It requires two
  unverified quasiconformal rigidity statements:
  - `uniformly-quasisymmetric-circle-groups-are-mobius-conjugates` (Markovic);
  - `h2-quasi-isometries-have-uniformly-quasisymmetric-boundary-maps`.
- I did not touch that route. This lane builds an independent second route with different, more
  elementary inputs.

## Literature gate (2026-09-16)

- Zaremsky's problem list (PDF dated July 12, 2026) still lists 2.18 as open.
- arXiv:2406.12982, Balasubramanya–Fournier-Facio–Zaremsky, *Hyperbolic actions of Thompson's group F
  and generalizations* (BFFZ in the nodes), v1 18 Jun 2024
  and v2 14 Apr 2026. Question 11.4 is still posed as open in v2. Text read on 2026-09-16:
  - Citation 1.1 and Definition 1.2: classification, focal versus general type, and ping-pong;
  - Definitions 1.5, 1.8, 1.10: pseudocharacter, agreeable, Busemann pseudocharacter;
  - Citation 1.12, "p(g) ≠ 0 iff g loxodromic" (statement only);
  - Citation 3.7: "Every subgroup of F_n is agreeable", citing [Cal07, FFL23]. So "every
    pseudocharacter of F is a character" is prior art. Calegari (2007) and Fournier-Facio–Lodha were
    not read.
- arXiv API keyword searches on 2026-09-16 (Thompson / hyperbolic plane / cobounded / hyperbolic
  structures) found no resolution. Checked: 2605.31538, 2607.10961, 2502.12590, 2310.09455.
- arXiv:1212.1230v2 (Dudko–Medynets), p. 10, was re-read. Verbatim: "the commutator subgroup of
  F_(n,r) is a simple group and the abelianization of F_(n,r) is isomorphic to Z^n [1, Section 4]".
  - Their bibliography: [1] = K. Brown, *Finiteness properties of groups*, JPAA 44 (1987) 45–75, and
    [2] = Cannon–Floyd–Parry.
  - **Referee flag.** The committed route `thompson-f-has-no-cobounded-action-on-hyperbolic-plane-proof`
    (lines 19–20) says their [1] is Cannon–Floyd–Parry. That is a misattribution; the quote itself is
    right. I did not edit that node.
- arXiv:1202.3585v2 (Caprace–Cornulier–Monod–Tessera, *Amenable hyperbolic groups*, 12 Nov 2013) was
  fetched and extracted on 2026-09-16. Section 3 does not assume properness. Quoted in the nodes:
  - the boundary definition;
  - Gromov's classification;
  - Proposition 3.1, a limit-set characterisation of the types, proved only in sketch;
  - Proposition 3.7 and Lemma 3.8: the Busemann quasicharacter is non-zero exactly on hyperbolic
    elements.

## What was established (graph nodes written by this lane)

1. `thompson-f-quasimorphisms-vanish-on-f-prime` (claim), with route `...-proof`, which requires only
   `thompson-f-has-no-free-subgroups`.
   - `F'` is perfect: simple by the Dudko–Medynets quote, and non-abelian because `F` is not
     elementary amenable.
   - Every homogeneous quasimorphism of `F` vanishes on `F'`. The proof is a disjoint-support
     swindle:
     - write `g ∈ F'` as a product of `m` commutators in `F'`;
     - push `n` copies apart with a fixed `h ∈ F` satisfying `h(t) > t`;
     - the product of the copies is a product of `m` commutators, so `n|β(g)| ≤ (2m − 1)D`.
   - check.sh reports it unlocked.
2. `busemann-null-isometries-have-no-boundary-contraction` (claim), with the direct route
   `...-proof` (`requires: []`).
   - The setting is any metric space with the four-point inequality, the sequential boundary, and
     boundary Gromov products as sup-liminf.
   - (i) The Busemann pseudocharacter is a homogeneous quasimorphism.
   - (ii) If `k` fixes `ξ ≠ a` and `p(k) = 0`, then no third boundary point `x` has
     `(k^n x|a)_o → ∞`.
   - Proof, stated from the four-point inequality alone:
     - the boundary estimates B1 (liminf ≥ product − 2δ), B2 (finiteness) and B3 (3δ triangle
       inequality);
     - the spread `[λ − δ, λ + δ]`, the Busemann cocycle, and homogenisation;
     - quasi-invariance of the horospherical product `P(y,w) = (y|w) − λ_y − λ_w`;
     - Claim A: `limsup λ_{y_i} ≤ (u|ξ) + δ`;
     - the final contradiction `(x_n|a) ≤ Q + 2(a|ξ) + 23δ`.
   - Revision this session: the defect bound `4D` for the homogenisation now carries its one-line
     justification.
3. `two-boundary-fixed-points-block-cobounded-qi-h2-actions` (claim), with the direct route
   `two-boundary-fixed-points-block-via-busemann-projection` (`requires: []`). New this session.
   - Put `f = b_ξ + b_η` and `π = (b_ξ − b_η)/2`.
   - `f ≥ −2Q`, by the triangle inequality along index pairs with `(z_i|z'_j) ≤ Q`.
   - `b(ho) + b(h^{-1}o) ≤ 2δ` for `h` fixing the point, by the spread lemma. So `f ≤ 2Q + 4δ` on the
     orbit, and `f ≤ B` everywhere if the orbit is `r`-dense.
   - The four-point inequality at base points `z'_j → η` gives
     `d(u,v) ≤ (f(u) + f(v))/2 + |π(u) − π(v)| + 2Q + 2δ`. So `π: X → R` is a quasi-isometric
     embedding.
   - Composing with `H^2 → X` contradicts an equilateral triangle of side `L ≥ R`, built in the
     hyperboloid model, via the chain argument.
   - No Morse lemma, no Manning, and no boundary topology is used.
4. `cobounded-qi-h2-actions-without-free-groups-are-focal` (claim, open hole with '## Attempts').
   - Item 1: the four-point inequality holds.
   - Item 2: `∂X ≅ S^1`, isometries act by homeomorphisms, and convergence forces the Gromov
     product to `∞`.
   - Items 3–4: `G` fixes `ξ`, and some `g` has exactly two fixed points, `ξ` among them.
   - The second pass closes the loxodromic-existence gap and the limit-set identification using the
     verified CCMT text:
     - Gromov's types are exhaustive by definition;
     - Proposition 3.1 identifies "uncountable limit set" with focal or general type;
     - coboundedness gives `Λ = ∂X` (elementary);
     - BFFZ ping-pong excludes general type;
     - BFFZ's "a loxodromic fixes precisely two points" supplies `g`.
   - **Still unverified:** items 1–2, i.e. non-proper boundary theory, `∂X ≅ S^1` above all.
5. `thompson-f-no-cobounded-qi-h2-action-via-busemann` (route for the locked hole). It requires
   nodes 1, 2, 3, 4 and `thompson-f-has-no-free-subgroups`. Steps:
   - Lemma H (Hölder) is proved in full;
   - the pseudocharacter vanishes on `F'`;
   - `F'` preserves orientation of `∂X \ {ξ} ≅ R`, by perfection;
   - an element of `F'` with a fixed point but acting non-trivially would contract a point onto a
     fixed endpoint, contradicting node 2(ii);
   - so `∂(F')` acts freely, is abelian by Hölder, and is trivial by perfection;
   - `∂(F)` is abelian and commutes with `∂g`, so it fixes `η` as well as `ξ`;
   - node 3 contradicts coboundedness.

Net effect: once check.sh confirms, the locked hole depends only on
`cobounded-qi-h2-actions-without-free-groups-are-focal` beyond established nodes. That claim is
textbook material (non-proper Gromov boundary of a space QI to `H^2` is a circle), and its
classification half is now backed by verified quotes.

## Approaches tried and where each dies

- **Uniformly bi-Lipschitz boundary maps.** Tried earlier in the lane: show that the boundary maps
  `∂(φ∘g∘ψ)` of the cobounded quasi-action are uniformly bi-Lipschitz on `S^1`, then run a Denjoy or
  Hölder argument.
  - This dies immediately. A radial stretch of `H^2` is a quasi-isometry whose boundary map, in a
    chart, is `x ↦ sign(x)|x|^α`. Conjugating an isometric action by it gives maps that are uniformly
    quasisymmetric but not bi-Lipschitz.
  - So only quasisymmetry survives, which is Markovic territory. Abandoned in favour of the Busemann
    product.
- **C2(ii) through the topology of `∂X`.** First draft: (ii) concluded "`k^n x → a`" and imported four
  boundary facts (I1)–(I4) from Bridson–Haefliger.
  - I restated (ii) with Gromov products, proved (I1)–(I3) in-body as B1–B3, and moved the topological
    (I4) into node 4. This makes node 2 a genuine direct proof.
- **C4 via the Morse lemma.** This is the first sketch, recorded in '## Attempts'. It needs the
  non-proper boundary extension of quasi-isometries and a bi-infinite Morse lemma, both unverified.
  - It was replaced by the Busemann-projection route above.
- **First intrinsic C4 attempt.** It needed Manning's theorem to bound `c_ξ + c_η`, and a "bounded `f`
  implies quasi-line" statement.
  - Both were replaced by elementary estimates: Steps 3, 5 and 4 of the new route.
- **Via Manning / CCMT Lemma 3.8 instead of node 2.**
  - `p(k) = 0` gives that `k` is not loxodromic.
  - A parabolic has one fixed point (BFFZ, statement only), so `k` fixes two points only if it is
    elliptic, and an elliptic isometry changes Gromov products boundedly. That gives node 2(ii).
  - Not used: the source arguments were not read, and node 2 is self-contained.
- **Avoiding node 4 item 2 (the circle).** The Hölder step needs a line order on `∂X \ {ξ}` and
  "topological convergence implies Gromov product → ∞".
  - I looked for an intrinsic order via Busemann data and found none quickly.
  - The honest remaining input is the non-proper boundary theory: the Morse lemma in geodesic
    hyperbolic spaces, giving quantitative comparison of Gromov products under a quasi-isometry, and
    hence `∂X ≅ ∂H^2 = S^1` with matching topologies.

## Sanity checks

- `BS(1,2)` acts coboundedly on `H^2`. It has no free subgroups, and its homogeneous quasimorphisms
  are homomorphisms (it is amenable). The route's hypotheses fail only at "`[G,G]` is perfect"
  (`[G,G] ≅ Z[1/2]`), and the argument indeed breaks at step 5 of the route.
- Scope of the reduction: any group with no non-abelian free subgroups, with `[G,G]` perfect, and with
  every homogeneous quasimorphism vanishing on `[G,G]`, has no cobounded isometric action on a space
  QI to `H^2`. This is modulo node 4.

## Weak points a referee should attack

1. Node 4, item 2: non-proper boundary theory, `∂X ≅ S^1` with the Gromov-product topology. Open, and
   the whole reduction rests on it.
2. Node 2, Step 7.1: choosing diagonal index pairs with `(y_i|w_i) ≤ Q` while keeping
   representatives, and then applying B1 and Claim A along the diagonal. I re-checked it this session
   and believe it is correct.
3. The new C4 route, Step 5: the spread lemma is applied to `h^{-1}z_i` versus `z_i`. It is correct
   because `h^{-1}ξ = ξ`.
4. Node 1 imports simplicity of `F'` from a verbatim quote whose own source is Brown (1987). Only the
   quote was read.

## Files

- research/thompson-f-quasimorphisms-vanish-on-f-prime.md
- research/thompson-f-quasimorphisms-vanish-on-f-prime-proof.md
- research/busemann-null-isometries-have-no-boundary-contraction.md
- research/busemann-null-isometries-have-no-boundary-contraction-proof.md
- research/cobounded-qi-h2-actions-without-free-groups-are-focal.md
- research/two-boundary-fixed-points-block-cobounded-qi-h2-actions.md
- research/two-boundary-fixed-points-block-via-busemann-projection.md
- research/thompson-f-no-cobounded-qi-h2-action-via-busemann.md
- research/artifacts/thompson-f-qi-h2-busemann-reduction-2026-09-16.md
- research/geodesic-spaces-qi-to-h2-have-circle-gromov-boundary.md
- research/cobounded-qi-h2-focal-via-dsu-classification.md
- research/qi-h2-circle-boundary-via-quantitative-morse-lemma.md
- notes/zaremsky-2-18-f-cobounded-action-on-hype-swarm-2026-09-16.md

## Third pass: Das–Simmons–Urbański

- Source: arXiv:1409.2155v7 (28 Jun 2016), fetched and text-extracted on 2026-09-16. It treats non-proper
  hyperbolic spaces throughout.
- New route `cobounded-qi-h2-focal-via-dsu-classification` for
  `cobounded-qi-h2-actions-without-free-groups-are-focal`. It requires
  `geodesic-spaces-qi-to-h2-have-circle-gromov-boundary` (new, open),
  `busemann-null-isometries-have-no-boundary-contraction` and
  `two-boundary-fixed-points-block-cobounded-qi-h2-actions`.
- The C2 claim now also states `|p − q| ≤ 18δ`, proved in Step 4 of its route. That bound is what
  excludes parabolic groups under coboundedness.
- The remaining hole is the circle boundary for non-proper `X` quasi-isometric to `H^2`. A proposed
  direct proof (G1)–(G6) is recorded in that claim. Its weakest step is the lower bound in (G3).
- Observation: the proof of DSU Proposition 6.2.14 asserts "#Fix(G) = 2 iff lineal". This seems to
  overlook groups that swap the two points. The route uses only the statement's trichotomy and handles
  the swap case by passing to an index-at-most-2 subgroup.

## Fourth pass: the circle boundary

- New route `qi-h2-circle-boundary-via-quantitative-morse-lemma`, with `requires: []`, for
  `geodesic-spaces-qi-to-h2-have-circle-gromov-boundary`. File:
  research/qi-h2-circle-boundary-via-quantitative-morse-lemma.md.
- Import: Gouëzel–Shchur, arXiv:1810.04579v1, Theorem 1.1. For a `(λ,C)`-quasi-geodesic `Q`, not
  necessarily continuous, in a four-point `δ`-hyperbolic space, and a geodesic `G` with the same
  endpoints, `HD(Q,G) ≤ 92λ²(C+δ)`.
  - The PDF text had to be decoded through its ToUnicode CMaps.
  - Relation glyphs come from the CM math font encoding: `6` is `≤` and `>` is `≥`.
- Everything else is elementary:
  - `(x|y)_o ≤ d(o,[x,y]) ≤ (x|y)_o + 2δ`, by the intermediate value theorem;
  - Gromov products are coarsely preserved by the quasi-isometry;
  - the boundary bijection;
  - boundary products are comparable;
  - explicit polar estimates in the hyperboloid model;
  - the topologies are identified through neighbourhood filters.

## Validation and self-review (2026-09-16, about 02:50 UTC)

- check.sh was run on all 12 research paths against landed 00e3d7646 and exited 0.
  - Computed status: established for `geodesic-spaces-qi-to-h2-have-circle-gromov-boundary`,
    `cobounded-qi-h2-actions-without-free-groups-are-focal`,
    `busemann-null-isometries-have-no-boundary-contraction`,
    `two-boundary-fixed-points-block-cobounded-qi-h2-actions`,
    `thompson-f-quasimorphisms-vanish-on-f-prime`,
    `thompson-f-has-no-cobounded-action-on-spaces-qi-to-h2` and the root
    `zaremsky-2-18-f-cobounded-action-on-hyperbolic-plane`.
  - No `requires: []` route was written into the root. It is reached through its existing route and
    the hole.
- Re-read line by line after the check, with no errors found:
  - the circle route, Steps 1–8, including the constants in (P), (H) and (G3);
  - the DSU route, Steps 2–7;
  - the main route, including Lemma H;
  - the C4 direct route, Steps 0–8.
- What a referee should attack first:
  - The imported statements behind the DSU route: Theorems 6.1.4 and 6.2.3, Proposition 6.2.14, and the
    ping-pong paragraph of Proposition 10.5.4.
    - Only their statements, and that one proof paragraph, were read.
    - Lemma 3.4.25 (continuity of the extension) is left to the reader in DSU.
    - The glyphs in Definition 3.3.2 and Proposition 4.2.16 were lost in extraction. Either reading of
      Proposition 4.2.16 suffices.
  - The Gouëzel–Shchur import (M): its statement was quoted verbatim, but its proof was not checked.
  - The claim's definition of `T` through the base `{N_t(u)}` is matched to DSU Section 3.4.2 by
    reading. The DSU route uses DSU's `T` only for uniqueness of limits, and the circle claim's own `T`
    for item 2.

## Referee (2026-09-16)

Adversarial referee pass on all 13 files of this lane. `git status` shows no other untracked lane files.

**What I checked**
- **Every route, line by line.** I re-derived all constants.
  - C1 swindle (`thompson-f-quasimorphisms-vanish-on-f-prime-proof`).
    - The support-pushing map `h` and its three affine pieces were checked.
    - So were the commutator count and `n|β(g)| ≤ (2m−1)D`.
    - Perfection of `F'` from simplicity plus non-abelianness was checked.
  - C2 direct route, Steps 0–7.
    - Spread `[λ−δ, λ+δ]`, cocycle `4δ`, defect `12δ`, `|q+c| ≤ 6δ`, `|p−q| ≤ 18δ`.
    - The shift `16δ` and Claim A.
    - The diagonal re-indexing in Step 7.1 and the final `Q + 2(a|ξ) + 23δ`.
  - C4 direct route, Steps 0–8.
    - `f ≥ −2Q` and the inversion estimate for `f` on the orbit.
    - The distance estimate making `π` a quasi-isometric embedding.
    - The hyperboloid equilateral triangle and the chain argument.
  - DSU route, Steps 1–7.
    - The parabolic exclusion `b ≥ −18δ − r` against `b(y) ≤ −18δ − r − 1`.
    - The lineal exclusion, through an index-at-most-2 subgroup that is `(r + d(so,o))`-dense.
    - The general-type exclusion through Schottky cyclic factors of infinite order.
    - Step 4 works under either one-sided reading of DSU Proposition 4.2.16.
  - Circle route, Steps 0–8.
    - The IVT bound `(x|y)_o ≤ d(o,[x,y]) ≤ (x|y)_o + 2δ`.
    - The constants (P), (H), (G3) with `A = 2Kδ + C + M + 2δ_H`.
    - The boundary bijection, the hyperboloid polar estimates, and the neighbourhood-filter
      identification.
  - Main route: Lemma H (Hölder), orientation preservation by perfection, contraction onto a fixed
    endpoint versus C2(ii), and the commuting-element step giving two global fixed points versus C4.
- **Imports, against independently fetched and extracted PDFs.**
  - Gouëzel–Shchur arXiv:1810.04579v1, Theorem 1.1: "HD(Q,G) ≤ 92λ²(C+δ)", matched verbatim, including
    non-continuous quasi-geodesics and four-point hyperbolicity.
  - Das–Simmons–Urbański arXiv:1409.2155v7, matched verbatim:
    - Convention 1;
    - Definitions 3.3.2, 3.4.1, 3.4.2, 6.1.1, 6.1.2, 6.2.2, 6.2.13 and 10.2.1;
    - (3.4.7);
    - Section 3.4.2 and Remark 3.4.15;
    - Proposition 3.4.18 and Lemma 3.4.25;
    - Proposition 4.2.16, which reads `≍_+`, so it is two-sided;
    - Theorems 6.1.4 and 6.2.3, Proposition 6.2.14, Lemma 10.2.2(i), and the "(A) ⇒ (F) for groups"
      paragraph of Proposition 10.5.4.
  - arXiv:2406.12982: the abs page confirms title, authors (Balasubramanya, Fournier-Facio, Zaremsky) and
    v2 of 14 Apr 2026.
- **Duplicates.** `bin/cairn search --similar` was run on the five new claim ids. It found only this
  lane's own nodes and the target chain, with no duplicate.
- **Novelty.** The nodes make no novelty claim beyond the target chain. "Every pseudocharacter of F is a
  character" is correctly credited as prior art (Calegari; Fournier-Facio–Lodha).
  - My own fresh web search could not run: the session's WebSearch budget was exhausted, and the arXiv
    API returned 429.
  - So the "no published resolution" conclusion rests on the lane's searches above: Zaremsky list of
    July 2026 and BFFZ v2 of Apr 2026, both still posing it as open.

**What I changed**
- These notes:
  - corrected the BFFZ author list, which was wrongly given as "…Genevois–Sisto";
  - added the circle route and this notes file to the Files list.
- `cobounded-qi-h2-actions-without-free-groups-are-focal`: marked the third-pass "Remaining hole" as
  closed later by `qi-h2-circle-boundary-via-quantitative-morse-lemma`.
- No mathematical content was changed.

**No mathematical error found. Residual trust surface**
- Statements, not proofs, of DSU Theorems 6.1.4, 6.2.3 and 6.1.10, Proposition 6.2.14, the Schottky
  paragraph of Proposition 10.5.4, and Lemma 3.4.25 (left to the reader in DSU).
- The Gouëzel–Shchur theorem (formally certified by its authors in Isabelle/HOL; proof not re-checked).
- Simplicity of `F'` via the Dudko–Medynets quote (classical: Brown 1987, Cannon–Floyd–Parry).
- All of these are standard literature imports stated verbatim with provenance.

**Not changed (committed nodes, outside this lane)**
- The root's '## Attempts' still describes the source reading as open via Markovic. That is stale now
  that the hole is computed established.
- The committed route `thompson-f-has-no-cobounded-action-on-hyperbolic-plane-proof` misattributes
  Dudko–Medynets [1]. It is Brown (1987), not Cannon–Floyd–Parry.

**Verdict.** Landed with minor fixes. Given the imports, `thompson-f-has-no-cobounded-action-on-spaces-qi-to-h2`
is established by the Busemann route, independent of the Markovic route. With the committed `H^2` claim,
Zaremsky Problem 2.18 / BFFZ Question 11.4 is answered no.
