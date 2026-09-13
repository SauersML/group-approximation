# audit-intro lane report

Lane `audit-intro` audits tex 1–784 of `non_mf_groups_exist.tex`: the abstract, the
Introduction, and `sec:compression-radical` (One-sided compression).

## Landed

- `798be51a3`: probe GREEN (tag `0913-025915-88913`, BUILT all three modules). The green bytes
  are identical to main, and all three modules are on the wire queue, carrier first:
  - `GroupApproximation/Manuscript/NonMFSentences/IntroConventionSentences.lean`, the carrier
    for three Introduction definition sentences that had none (defects 1–3 below).
  - `GroupApproximation/Manuscript/NonMF/Audit/Intro.lean`, the permanent gate for tex
    1–345 (96 audit commands).
  - `GroupApproximation/Manuscript/NonMF/Audit/Sec2.lean`, the permanent gate for tex
    346–784 (166 audit commands).
- The census row corrections `metadata/nm-census-rows/audit-intro.tsv` land in the same commit
  as this report.
- `654163349`: probe GREEN (tag `0913-041408-72676`, BUILT). The module is on the wire queue:
  - `GroupApproximation/Manuscript/NonMFSentences/IntroWitnessSignSentence.lean`, the carrier
    for tex line 134 at the literal `W` (defect 4 below).
  - The module carries its own `#audit_closed_axioms` gate.
  - It needs the 09-09 orphan `Sofic/AffineHNNBaseRealization` wired first.
- `9d3013e41`: probe GREEN (tag `0913-091959-40244`, BUILT). The module is on the wire queue:
  - `GroupApproximation/GGT/VanKampen/Estimating/OsinLemma94RegionSideCount.lean`, a sub-piece
    of the h94 count of `osinLemma94Section_of_planarPieces`, assigned by hull-count94 (see
    below).
  - `#audit_axioms` follows all five declarations.

## Help: the h94 count (hull-count94)

After the 08:30 restart the lead moved this lane to help hull-count94 with `PolygonCount`.
hull-count94 assigned one sub-piece with a fixed statement, which it consumes from
`Estimating/OsinLemma94PolygonCount.lean`.

- `RealizedSectionFamily.regionFacingUnbound S i`: the unbound darts of cell `i` whose reverse
  lies in a selected region.
- `RealizedSectionFamily.sum_card_regionFacingUnbound_le`: if no relator cell reads the
  identity, then `∑ i, #(regionFacingUnbound i) ≤ 2 ε |M|`.
  - The reverse of such a dart is a boundary dart of the region, since no region contains a
    relator face (`faces_not_mem_of_value`).
  - Along `boundary_decomposition` it is on neither arc. A dart of the source arc, or of a
    relator-cell target arc, lies on that cell (`cell_face_injective`) and is bound. An outer
    dart belongs to no relator cell (`face_ne_outer`).
  - So the reverse is on the right or left side (`alpha_mem_sides_of_mem_regionFacingUnbound`).
    `alpha` is injective, distinct cells have disjoint darts, and each side has at most `ε`
    darts.
- Helpers: `Embedded.mem_targetBoundaryDarts_cases` and
  `RealizedSectionFamily.mem_cellDarts_of_mem_regionFacingUnbound`.

A model-test observation for `Covers`, passed to hull-count94: a region has nonempty G-faces, so
an unbound dart whose reverse lies directly on another relator cell faces no region side. Such
darts are excluded only through the O-equivalent edge doubling (`false_of_unbound_shared_edge`
in `OsinUnboundSharedEdge`), so the realization piece has to keep them out.

### Pinched relator cells (read-only check, sent to hull-count94 and main)

hull-count94 asked whether pinched relator cells can occur under `GloballyDistinguishedSectionFamily`
and `DartMinimal`. A pinch means a relator walk `[.., e1, x, e2, ..]` where the value-one subword
`x` closes up at a vertex `v` and encloses a `G`-face `B`. No Lean was written. Line numbers are
on `cb0ec2d30`.

- Two surgeries relate the pinched and unpinched diagrams. Neither is on main.
  - The un-pinch splits `v` at a corner of `B` and a corner of the face `P` across `e2`.
  - The inverse identifies two corners of one polygon.
  - Both keep the boundary word, the cells and their words, and the regions. So they keep weight,
    card, `unboundSum` and `dartCount`.
- **(a) Across the corner is an unselected `G`-face.**
  - Today this is excluded, but only through the loop region `{B}`: its source and target arcs
    lie on the same cell and its sides are empty. `RespectsSections` constrains only
    `target = none`, and the route is the one `false_of_digon_toward_cell` takes with `i₂ = i`.
  - After LoopCut ruling (A) lands, (a) is not excluded. `S` is optimal and dart-minimal iff its
    pinched copy is.
  - Model: `t` disjoint value-one subwords on one (A1) arc raise `SideBudget` by `2t` with `n`
    fixed. The bubbles are the cell analogue of the boundary bubble in the `SideBudget` model
    test.
  - The respelling this needs: (A1) sides skip value-one excursions, as F1 rules for (A2).
- **(b) `P` lies in a selected region.**
  - (b1) The arc ends at the pinch. Un-pinching and extending the arc through `x` raises the
    weight, so this is excluded, but the Lean proof needs the un-pinch.
  - (b2) The pinch lies inside a short side. This is not excluded after (A). There are at most
    `24 ε n` such vertices, which is harmless now that K comes after ε.
- **(c) Across the corner is the exterior or another cell.** This is excluded without the pinch,
  by `false_of_unbound_shared_edge`. With the same cell on both sides it is excluded today through
  `i₂ = i`, and after (A) it becomes the same-cell `hloop` site.
  - Pendant spurs `l · inv l` are allowed: `IsSmallCancellation` and `OsinCCondition` have no
    reduction field.
  - They are also dart-minimal. So after (A), an `hloop` spelled "no unbound edge with the cell on
    both sides" is false in models.

### Model test of the patched side budget (sent to hull-count94)

main ruled three things:
- `SideBudget` skips value-one excursions on (A1) sides as well as (A2).
- One-sided bubbles that read a value-one subword of a relator are dropped.
- The patched Prop is model-tested on the pinched-cell model before it lands.

No draft Prop was on main (`594fe2988`), so the test uses the spelling in the ruling.

- **Model.**
  - One cell (`n = 1`), `λ = 1/8`, `c = 3`.
  - The relator is `g_1·abc·g_2·abc·…·g_{t+1}`, with `abc = 1` and generic geodesic `g_i`.
  - The pinch is applied at each `abc` on an (A1) arc of a maximal polygon `P`. It keeps every
    hypothesis of the count Prop.
  - `t` is unbounded, since `W` has no upper length bound.
  - A pendant spur inside the cell splits the side the same way, with no bubble.
- **Budget: passes, given two spelling points.** Today `∑ sideCount` rises by `2t`.
  - A class is a maximal run of consecutive sides on one cell whose gaps in the cell walk have
    value one. The gap is automatically a closed subwalk. Counting runs needs no `Maximal` skip
    clause.
  - A one-sided bubble is a polygon with exactly one class, of kind (A1). The (A1) filter alone
    keeps every bubble.
- **Covers: fails under one spelling and passes under another.**
  - First spelling: the class word concatenates the polygon's side words.
    - Then nothing covers the `3t` bubble darts.
    - With `t = L` and `ρ ≥ (8L)²`, Lemma 9.4 is not contradicted, yet `Covers` fails for every
      `L` fixed before `ρ`.
    - Keeping the bubbles in `Covers` but not in the budget does not help, since
      `dense_of_covers` and the metric Prop run over one family.
  - Second spelling: the class word is the reversed cell arc, gaps included. This passes.
    - The corners agree.
    - The arc is quasi-geodesic, as a subword of a rotation of the relator.
    - The gap darts are covered.
    - Only a gap where a class arc or a region arc ends stays uncovered. Each such gap is a
      closed value-one subword, of length at most `(c + 2)/λ`.
    - There are at most `2(K + 24) n` of them, so `L = 24ε + 2(K + 24)⌈(c + 2)/λ⌉` works.
- **Open for hull-count94.**
  - Under the second spelling, a connector endpoint can lie on a gap dart, off the polygon walk.
  - The Case 1 users must accept that position: either a region that contains the bubbles, or
    the un-pinch first.
  - Neither half needs the (darts, faces) minimality.

## The rows in range

There are 191 census rows.

- Tex 1–345: 78 rows (35 formalized, 12 definition, 14 structural, 13 attribution, 4 partial).
- Tex 346–784: 113 rows (88 formalized, 13 definition, 12 structural).

1. **Reachability.** Every declaration named by a formalized, definition, structural or
   attribution row in range exists on origin/main, and none is `private`. Modules the root did
   not yet reach were already on the wire queue.
2. **Gate.**
   - Each named-proposition endpoint gets `#audit_closed_axioms`, and every other named
     declaration gets `#audit_axioms`.
   - A declaration named by several rows is audited once, at its first row.
   - `Audit/Sec2` does not repeat declarations that `Audit/Intro` already audits.
   - The four `partial` rows are not gated, and `Audit/Intro` lists them in its module
     docstring.
3. **Reading against the print.** Outside the rows listed under Walls, the carriers state the
   printed sentences at the printed generality. No binder stands for a cited result.

## Defects

1. **Fixed: `be1769283b2f`, L112.** The sentence "products of $C^*$-algebras mean bounded
   products, and $\bigoplus$ denotes the ideal of norm-null sequences" had no carrier.
   - `PrintedBoundedProductsNullIdeal` covers every sequence of C⋆-algebras.
     - The product is `lp A ∞`: its members are exactly the norm-bounded sequences, and it is a
       C⋆-ring.
     - The norm-null sequences form a closed two-sided `*`-ideal.
     - The norm matrix corona is the quotient by exactly this ideal.
   - Closed proof: `manuscriptSentence_boundedProductsNullIdeal`.
2. **Fixed: `651e122a919e`, L134.** The sentence "where $V$ is the ascending HNN extension …
   with $[c_x,c_y]=\varepsilon$ for $x\ne y$" had no carrier.
   - `PrintedCliffordWitnessGroup` is stated over the literal `ℤ³ ⋊ SL₃(ℤ)` and the doubling
     `α`. Its clauses:
     - the matrix action and `α(v,A) = (2v,A)`;
     - `ι` injective and `t ι(g) t⁻¹ = ι(α g)`;
     - the HNN universal property;
     - `X = V/ι(Γ)` with left multiplication;
     - `Cl(X)` generated by `ε` and the `c_x`, with involutions, `ε` central,
       `[c_x,c_y] = ε`, and the presentation's universal property;
     - `W = Cl(X) ⋊ V` through the induced action.
   - Closed proof: `manuscriptSentence_cliffordWitnessGroup`.
3. **Fixed: `ec81a8c16b64`, L156.** The sentence "We use the group commutator convention
   $[g,h]=ghg^{-1}h^{-1}$" had no carrier. The carrier is `PrintedCommutatorConvention`, with
   closed proof `manuscriptSentence_commutatorConvention`.
4. **Fixed: `9930600167a4`, L134.** The sentence "Every homomorphism from $W$ to an MF group
   kills $\varepsilon$" was carried only by the general theorem
   `CliffordWitnessDirectDefect.manuscriptMapSignEqOneOfIsOperatorMFTarget`. Main had no
   specialization to the literal `W`, and no property (T) for `AffineSL3Doubling.Gamma`.
   - `PrintedWitnessMFHomKillsSign` is stated at `PrintedW` and `ε = inl (sign X)`. It covers
     every operator-MF target, and every countable target that is MF in the printed sense of
     tex lines 86–99 (`IsCDEOperatorMF`).
   - Property (T) for `ℤ³ ⋊ SL₃(ℤ)` needs no new theorem.
     - The new `gammaEquiv : AffineSL3Doubling.Gamma ≃* ExplicitLinearModel.gammaBar` sends
       `(v, A)` to `[[A, v], [0, 1]]`.
     - Surjectivity is the affine normal form `AffineHNNBase.gammaBar_affUnit_form`.
     - (T) then transfers from `CommutingLampCollapse.gammaBar_hasKazhdanPropertyT` by
       `HasKazhdanPropertyT.of_mulEquiv`.
     - The EJZ route was not needed.
   - Closed proof: `manuscriptSentence_witnessMFHomKillsSign`.

Defects 1–3 are corrected to `definition` in `metadata/nm-census-rows/audit-intro.tsv`.
Defect 4 stays `formalized`, with the new carrier.

## Walls (reported to the lead)

- `a16637da7249` (L66): partial.
- `61827aea7807` (L187): partial. `HSVanishes` / `manuscriptPrintedNormalKazhdan` (hs-vanishes).
- `0f22bdbc4184` (L285) and `dce7a9ff4e83` (L291): partial. These rows carry the binders
  `hgreendlinger`, `hbridge`, `hKO` and `hW` (torsion-free Theorem C).
- `27e0c2f96db3` (L291): attribution row that names `LiteratureInputs`.
- `837b7cffa562` (L99): baseline carrier-data for `IsStronglyOperatorMF`, resolved as a
  contrapositive.
- `c36b6021a802` (L572): `HSVanishes` carrier-data.

## Open

- Wiring (root-wire): `IntroWitnessSignSentence` after `Sofic/AffineHNNBaseRealization`.
- Once both are rooted, `Audit/Intro` can gate the new endpoint under L134 as well.
- `OsinLemma94RegionSideCount` is consumed: `OsinLemma94PolygonCount` imports it and closes
  `osinLemma94PolygonCoversInput` with `sum_card_regionFacingUnbound_le` (hull-count94,
  `2b2e16cc6`). Wiring `PolygonCount` pulls it in.
- The remaining count residual is `OsinLemma94PolygonSideBudgetInput`. K now comes after ε
  (`9f8779c4e`).
  - main ruled the (A1) excursion skip and the bubble drop.
  - The model test above went to hull-count94, together with the class-word spelling that
    `Covers` needs.
  - The un-pinch surgery is not on main.
  - This lane waits for hull-count94's draft patched Prop, and re-runs both tests on it before it
    lands.
