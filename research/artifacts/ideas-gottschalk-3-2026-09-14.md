# ideas-gottschalk-3 — synthesis round for Gottschalk's conjecture (2026-09-14)

Lane: ideas-gottschalk-3. Goal node: `gottschalk-surjunctivity-conjecture` (OPEN). This round reads what the
gk3-* team and hl-gottschalk-dynamics landed today, combines lanes, kills weak combinations, and executes the
best survivor. Nothing here decides the conjecture. Results are unreviewed.

## 1. Sources read (origin/main, 09-14)

- ideas-gottschalk-2 `260e8770c`: `nonamenable-groups-carry-arrow-shift-strict-automata`,
  `linear-strict-pairs-are-transposes-of-post-surjective-automata`.
- gk3-dual-surjunctivity `2b23c4fc8` and gk3-post-surjective-decoders `9062f988c`:
  `post-surjective-decoders-convert-strict-pairs-to-dual-failures`, `decoders-lift-changes-away-from-infinite-defect-chains`.
- gk3-alphabet-descent `0a2fdc1cc`: `passive-fixing-injective-automata-are-surjective`,
  `ec-groups-share-the-nonsurjunctive-alphabet-sizes`, `some-nonsurjunctive-group-gives-a-binary-one`.
- gk3-binary-descent-2 `58f2fff34`: `modular-matrix-failures-descend-to-scalars-over-g-times-p`,
  `binary-shifts-over-odd-fibers-split-off-the-augmentation-shift`.
- gk3-approx-surjunctive `64d0dde19`: `uqs-groups-are-closed-under-amenable-extensions`; the kernel ladder
  `surjunctivity-of-a-local-class-is-reflection-kernel-membership`.
- gk3-binary-fullness `f4245dcc9`…`8d107797e`: `rank-deficient-tower-coverings-decide-binary-cyclic-corner`,
  `two-order-three-coset-ideals-never-contain-one`, the V census.
- gk3-ternary-fullness `903b6ac2a`: chain audit and linear screens.
- gk3-bernoulli-preservation `7de7861fa`: `binary-four-address-single-flip-balance-census` (26 strongest candidates).
- gk3-leavitt-nonlinear `0363ccee5`, `e39a422ba`, `c546cda87`: `two-rectangle-surjunctive-images-kill-all-designs`,
  `leavitt-rooted-defect-window-carries-no-strict-design`, `small-leavitt-windows-carry-no-strict-design`.
- gk3-transvections `2253e8c8d`, `513df875e`, `ff5d0c183`: the Jacobson half-line reduction.
- gk3-rokhlin-tester `c76d0e0d3`: `rokhlin-permanence-toolkit-certifies-only-sofic-groups`.
- hl-gottschalk-dynamics `d6394b5c7`, `ee25efafa`, `a40b790b0e`: strict-pair memory conditions; binary memory ≥ 4.
- Older anchors: `strict-pairs-transfer-to-table-realizations`, `compressed-coset-shifts-carry-strict-equivariant-embeddings`,
  `gottschalk-reduces-to-fg-simple-kazhdan-groups`, `amenable-decoder-memory-forces-surjectivity`.

## 2. Synthesis map

**Mechanisms that do produce strict maps (none on a full shift):**
- M1 arrow-shift hotels, fibred over `X_S` with no finite orbits (nonamenable groups).
- M2 compressed coset shifts `A^(G/H)` with `uHu⁻¹ < H` (even over amenable `BS(1,2)`).
- M3 linear one-sided inverses in `M_n(F_p[G])`: none known. Tower coverings reduce the binary cyclic corner to a
  covering problem; the V census and the ternary screens found nothing.
- M4 Leavitt compression windows: every small window tested is dead through separating PSL(3,2) images of its
  two-rectangle table group.

**Barriers, by lane:**
- B1 finite orbits: no full shift maps equivariantly into `X_S`; any argument using only Bernoulli-type
  properties would also make coset shifts surjunctive, so a proof must use freeness of the regular action.
- B2 finite pieces: passive fixing (sitewise) makes injective automata surjective.
- B3 counting certifies membership only in `N_sof`; Rokhlin permanence produces only sofic groups.
- B4 table groups: a window dies once its two-rectangle table group has a surjunctive image separating reverse
  products; strict data transfer to every realization of the table.
- B5 decoders lift finite output changes except along infinite chains of defect windows.
- B6 small memories: binary memory ≥ 4; memories need `s·m = 1` or positive relations; 664/859 four-address
  unbalanced classes die over every group; amenable decoder memory forces surjectivity.
- B7 alphabet: e.c. groups have every nonsurjunctive alphabet size; linear matrix failures descend to scalars
  over `G × P`.

**Where barriers combine.** Every mechanism M1–M4 is strict because information moves into space that the base
provides for free (arrows, coset compression, Leavitt isometries). On a full shift that space has to be made
from the data. B1 says constant data provide nothing. B2 says that if the automaton leaves the passive part of a
configuration alone, configurations with finitely many active sites form finite invariant pieces, and strictness
dies. So the one place a full-shift counterexample can live is where the automaton **activates passive
regions**. Section 4 makes this precise and removes a hypothesis from B2.

## 3. Sixteen combined ideas

| id | combination | mechanism | kill test | verdict |
|---|---|---|---|---|
| I1 | B1 × B2 × M1 | passivity defined by neighbourhood patterns; fixed passive sites plus no new active sites give finite invariant pieces | find an injective non-surjective map satisfying both | **executed**: theorem, §4 |
| I2 | B2 audit | the sitewise hypothesis "active sites stay active" is never used by the pieces | exhibit the piece step failing without it | **executed**: redundant, §4 Cor 1 |
| I3 | I1 × M1 on simple hosts | spread activity from the boundaries of constant patches along paradoxical decompositions computed from boundary data; decoder reads the boundary back | collisions of spreads from distinct boundaries must be resolved injectively inside bounded creep `Act(Φx) ⊆ Act(x)W⁻¹` | **survives**: best next lane |
| I4 | B2 on asymptotic classes | strict `τ` maps asymptotically constant configurations into themselves, injectively, not onto; forward orbits of missed points are infinite | does it give an invariant? | killed: restatement of density plus closed image |
| I5 | B5 × I1 | activity creation should force infinite defect components, hence decoder failure | creep is bounded each step; components can stay finite at every finite stage | parked: no implication either way |
| I6 | M2 → full shift | pull the coset-shift embedding back through right-`H`-invariant configurations | automata preserve right-`H`-invariance only when `H` is normal, and simple hosts have none | killed |
| I7 | B4 × B7 | e.c. hosts realize every strict table | restates the kernel ladder | killed: known |
| I8 | M3 × B3 | Sylvester rank as linear Rokhlin entropy | site pullbacks are discontinuous in the rank metric (main) | killed for nonlinear automata |
| I9 | M3 × B7 × duality | linear Gottschalk in characteristic `p` holds iff `F_p[K]` is directly finite for one e.c. `K` | elementary restatement of direct finiteness | survives, low value, not executed |
| I10 | B6 × B4 | four-address candidates whose two-rectangle table groups are free products of cyclics are dead (freeness corollary) | needs the decoder window, not only the forward memory | handed to gk3-four-address-survivors |
| I11 | B1 on simple hosts | on infinite simple groups the only finite orbits are constants, so arrow computation fails only on constant patches | no obstruction beyond constants | folded into I3 |
| I12 | M4 × I1 × B4 | a creeping design's window must have a hinge word in every sofic kernel | filter only | survives as census filter, §5 |
| I13 | B5 × B2 | decoders that fix passive sites | no mechanism | killed |
| I14 | B4 × B6 × I1 | one normal form for strict designs: memory ≥ 4 (binary), `s·m = 1` or positive relations, nonamenable decoder memory, hinge in `N_sof`, activity creation | checklist, not a theorem | survives as filter, §5 |
| I15 | Bernoulli × I1 | creeping automata push Bernoulli measure onto a null set | long constant patches have positive density, no invariant found | killed |
| I16 | B7 × I2 | codings over `G × F` must rewrite a constant fibre | follows from I2 | folded into §4 Cor 2 |

## 4. Executed: local passivity barrier

**Theorem** (`local-passivity-preserving-injective-automata-are-surjective`, route `local-passivity-surjectivity-proof`,
ESTABLISHED). Let `W ∋ 1` be finite and `P ⊆ A^W` contain a constant pattern. Put
`Act(x) = { g : (g⁻¹x)|_W ∉ P }`. An injective cellular automaton `Φ` on `A^G` with
(1) `Φ(x)(g) = x(g)` for `g ∉ Act(x)` and (2) `Act(Φ(x)) ⊆ Act(x)` is surjective. No property of `G` is used.

**Proof idea.** For `x₀` with finite active set `E`, the set of configurations equal to `x₀` off `E` with active
set inside `E` is finite and invariant; injectivity makes it a bijection, so `x₀` is in the image. These
configurations are dense (extend any pattern by the constant symbol), and the image is closed.

**Corollaries.**
1. `injective-automata-fixing-passive-sites-are-surjective` (route `passive-site-fixing-surjectivity-via-local-passivity`):
   for `W = {1}`, (2) follows from (1). The landed `passive-fixing-injective-automata-are-surjective` carries a
   redundant second hypothesis; its proof node's remark "both hypotheses are needed" refers to its choice of pieces.
2. A strict automaton on `(A ⊔ D)^G` must rewrite some `D`-site on some configuration. Binary codings over `G × F`
   must rewrite a constant fibre.
3. With `P` the constant patterns: a strict automaton that is the identity on locally constant sites must make some
   locally constant site non-constant in the output. Under (1) alone the creep is bounded in one step,
   `Act(Φ(x)) ⊆ Act(x) W⁻¹`, so weakening (2) to bounded growth is the same as dropping it.
4. Arrow-field hotel pullbacks are undefined on constant patches (B1). If they act as the identity there, Corollary 3
   says they are strict only if they activate constant patches from their boundaries.

**Model tests.** The left shift on `{0,1,*}^Z` violates (1) and is bijective. The rule "output `*` at or next to a
`*`" satisfies (1) and is not injective. M1 and M2 are not on full shifts with fixed passive regions.

## 5. Combined filter for census lanes (I12, I14)

A strict design on a full shift over `G` has all of:
- memory `|M| ≥ 4` over two symbols (a40b790b0e), and `s·m = 1` for some decoder letter or positive relations in both
  memories (ee25efafa);
- a nonamenable decoder memory group (`amenable-decoder-memory-forces-surjectivity`);
- a two-rectangle hinge word in the kernel of every homomorphism into a sofic group (Cor 1 of
  `two-rectangle-surjunctive-images-kill-all-designs`);
- on some configuration, a rewrite of a passive site or the activation of a passive neighbourhood (§4), for every
  choice of passive pattern set containing a constant pattern that the design leaves alone.

## 6. Exact gap and best next lane

- **G1 (open).** Can hypothesis (2) be dropped for `|W| > 1`? Equivalently: is every injective automaton that fixes
  every locally passive site surjective? A counterexample is a strict design with bounded creep into passive regions.
  A proof would remove all designs that leave locally constant regions untouched.
- **G2.** Strict designs of shape I3: boundary-driven spreading into constant patches on a nonamenable host (e.g. a
  finitely generated simple Kazhdan host, where constants are the only finite orbits). The decoder must reconstruct
  the pre-spread boundary; the collision problem between spreads from different boundaries is the kill test.
- **Best next deep lane:** `gk3-activity-creep`. Decide G1. Construct candidates of shape I3 over a nonamenable group
  with exact decoders on small windows (MSI, reuse the gk3-strict-census-4 SAT engine with the §5 filter), or prove
  G1 by finding invariant finite pieces that allow bounded creep.
