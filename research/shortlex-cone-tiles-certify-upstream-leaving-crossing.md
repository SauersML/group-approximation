---
rg: 2
id: shortlex-cone-tiles-certify-upstream-leaving-crossing
kind: claim
title: For a hyperbolic group, lex-least descent turns the horofunction compactification into a radius-one factor subshift whose ShortLex cone tiles split exactly into translates contained in the tile, with finitely many types; so upstream certification is not the F_infinity gate, and what remains is crossing, i.e. square filling between descent trees at different bases, which for Kazhdan inputs cannot come from a median join
requires:
  - hyperbolic-groups-have-sft-horofunction-compactifications
  - v-stabilized-horofunction-hosts-need-upstream-certification
  - v-times-subshift-full-group-finiteness-is-horizontal
distinct_from:
  v-stabilized-horofunction-hosts-need-upstream-certification: that shows ball-pattern tiles of horofunctions fail upstream certification (UC) because descents branch, and names UC as the missing insight; this removes branching by a canonical (lex-least) descent, proves UC exactly for the resulting cone tiles, and locates the real gate in crossing.
  hyperbolic-groups-lie-in-the-rigid-compactification-class: that proves rigidity of the distance-gradient SFT via drop chains along one geodesic; this is about finiteness, and the chains along one geodesic are the nesting chains of cone tiles, while the open part is between different geodesics.
  pentagon-reflection-group-fails-cone-matching-at-wall-ends: that finds the failure of atom matching at branch points; this is the same failure, now isolated as crossing of two exact tile trees rather than as inexact tiles.
---

**Status.**
- **ESTABLISHED (lane proof, bh-finf-hyp, 2026-09-19; elementary; not reviewed):** Theorem items 1–3.
- **Remark / route (not proved):** item 4 and the building route in "Next".
- No computation was run (MSI Slurm is blocked for the group). No priority is claimed.
- Inputs: ShortLex automaticity of hyperbolic groups for every finite ordered generating set
  (Epstein et al., *Word processing in groups*, Thm 3.2.2 with Cannon; recalled, not re-read), and the
  Myhill–Nerode theorem.

## Setting

- `Γ` is a group with a finite symmetric generating set `S`, totally ordered. `SL(g)` is the ShortLex-least
  geodesic word for `g`, and `L_SL` is the set of all `SL(g)`.
- Standard facts: prefixes and suffixes of words in `L_SL` lie in `L_SL`. (If a prefix or suffix could be
  replaced by a ShortLex-smaller word for the same element, so could the whole word.)
- **ShortLex cone of `w`:** `C(w) = {v ∈ Γ : SL(w)·SL(v) ∈ L_SL}`. Then `SL(w)SL(v) = SL(wv)` for `v ∈ C(w)`.
- **Cone tile:** `T(x, w) = x·C(w) ⊆ Γ`, for `x, w ∈ Γ`.
- **Letter field:** for `g ∈ Γ` and `x ≠ g`, `a_g(x)` is the first letter of `SL(x^{-1}g)`; put `a_g(g) = ∗`.

## Theorem

1. **Exact splits (any group).**
   - `γ T(x,w) = T(γx, w)`, and `T(x,w)` depends on `w` only through the set `C(w)` (its *cone type*).
   - `T(x,w) = {x} ⊔ ⨆_{s ∈ S ∩ C(w)} T(xs, ws)`, a partition.
   - Hence `T(xu, wu) ⊆ T(x,w)` for every `u ∈ C(w)`. The pieces of a tile are translates of tiles, contained
     in it, with no reference to where the tile came from. This is upstream certification (UC) in the sense
     of `v-stabilized-horofunction-hosts-need-upstream-certification`, exactly.
2. **Finite type (hyperbolic `Γ`).** There are finitely many cone types, so finitely many `Γ`-orbits of tiles
   `T(x,w)` up to the identification in item 1.
3. **The model is a factor subshift of the horofunction compactification.**
   - `a_g(x)` is the least `s ∈ S` with `d(xs, g) < d(x, g)`. So `a_g = Φ(∇d_g)` for a sliding block code `Φ`
     of radius 1 applied to the distance-gradient field.
   - Let `Ω ⊆ (S ⊔ {∗})^Γ` be the closure of `{a_g : g ∈ Γ}`, and `∂Ω` its non-isolated part. Let `Y` be the closure
     of `{∇d_g}`, the distance-gradient compactification of `hyperbolic-groups-have-sft-horofunction-compactifications`,
     and `∂Y` its limits along `g_n → ∞`. Then `Ω = Φ(Y)` and `∂Ω = Φ(∂Y)`.
   - Every cone tile is a cylinder over a geodesic segment: `g ∈ T(x,w)` iff following `a_g` from
     `p = xw^{-1}` spells `SL(w)`. So the tiles extend to clopen subsets of `Ω`. Item 1 holds there, with
     `{x}` deleted on `∂Ω`.
4. **What is left (remark).** Iterated splits of one tile never cross: they form the rooted tree of subtiles at
   its base. Crossing appears only between **different bases**.
   - The whole space has one split for each base `x`: `Ω = {x} ⊔ ⨆_s T(xs, s)`.
   - A finite shadow basis (`one-scale-filling-decides-fp-of-v-times-subshift-hosts`, Part 2) needs common
     refinements of the descent trees at two bases `x ≠ x'`, and a finite spine of minimal ones.
   - That is the only hypothesis of the Thumann route not supplied by items 1–3.

## Proofs

**1.**
- **Equivariance** is immediate from `T(x,w) = x·C(w)`.
- **Split.** Let `v ∈ C(w)`, `v ≠ 1`, and `SL(v) = s·v''`.
  - `SL(w)s` is a prefix of `SL(w)SL(v) ∈ L_SL`, so `s ∈ C(w)` and `SL(ws) = SL(w)s`.
  - `SL(v'')` is the suffix `v''`, and `SL(ws)SL(v'') = SL(w)SL(v) ∈ L_SL`. So `v'' ∈ C(ws)`, and
    `xv = (xs)v'' ∈ T(xs, ws)`.
  - Conversely, let `s ∈ S ∩ C(w)` and `v'' ∈ C(ws)`. Then `SL(w)·s·SL(v'') ∈ L_SL`. Its suffix `s·SL(v'')` is
    in `L_SL`, so it equals `SL(sv'')`, and `sv'' ∈ C(w)`.
  - Disjointness: the first letter of `SL(v)` is determined by `v`.
- **Nesting.** Apply the split along the letters of `SL(u)`. The tile at the node `u` of the tree based at `x`
  is `T(xu, wu)`.

**2.**
- `v ∈ C(w)` iff `SL(v)` lies in the residual `SL(w)^{-1}L_SL = {y : SL(w)y ∈ L_SL}`. Every such `y` is a
  suffix of a word of `L_SL`, so it lies in `L_SL` and is `SL(v)` for its value `v`.
- So `C(w)` is determined by the residual of the regular language `L_SL` at the word `SL(w)`.
- Myhill–Nerode: a regular language has finitely many residuals.

**3.**
- **The letter as a gradient.** Words of `L_SL` are compared first by length, then lexicographically. So the
  first letter of `SL(h)` is the least `s` beginning some geodesic word for `h`, i.e. the least `s` with
  `|s^{-1}h| = |h| − 1`. With `h = x^{-1}g`, this is the least `s` with `d(xs, g) = d(x, g) − 1`.
- **Closures correspond.** `Φ` is continuous and `Y` is compact, so `Φ(Y)` is closed. It contains every `a_g`,
  hence `Ω`. It lies in `Ω`, because `Φ(∇d_g) = a_g` and the `∇d_g` are dense in `Y`.
- **Boundaries correspond.** The cylinder "`∗` at `g`" meets `Ω` only in `a_g`, so the `a_g` are exactly the
  isolated points. The other points are limits of `a_(g_n)` with `g_n → ∞`. By compactness these are the images
  of `∂Y`.
- **Tiles are cylinders.**
  - Following `a_g` from `p` traces `SL(p^{-1}g)`: if `SL(p^{-1}g) = s_1 s_2 ⋯`, then
    `SL(s_1^{-1}p^{-1}g) = s_2 ⋯` by the suffix property.
  - `g ∈ T(x,w)` means `x^{-1}g ∈ C(w)`, i.e. `SL(w)SL(x^{-1}g) ∈ L_SL`, i.e. `SL(p^{-1}g)` begins with `SL(w)`.
    Conversely, if `SL(p^{-1}g) = SL(w)·y`, then `y ∈ L_SL` is a word for `x^{-1}g`, so `y = SL(x^{-1}g)`.
- On `∂Ω`, delete the isolated point `{x}` from the split. `∎`

## What this changes

- **The named missing insight is supplied.** Synthesis v8, open problem 2, names "upstream certification for
  branching descents". Branching was an artefact of reading all downhill directions.
  - The lex-least descent is canonical, and it is local: radius 1 in the gradient.
  - Its cone tiles are exact, with finitely many types. This holds for every hyperbolic group, Kazhdan ones
    included.
- **The obstruction does not disappear. It moves to crossing.**
  - The horofunction host is finitely presented (`v-stabilized-full-contracting-rsgs-are-finitely-presented`,
    for `Γ ∗ Z`).
  - By `v-times-subshift-full-group-finiteness-is-horizontal`, `F_∞` of such a host is exactly essential
    connectivity of the domain filtration. For the ShortLex model, that is filling between descent trees at
    different bases.
- **Calibrations.**
  - *Free group on a basis:* every cone tile is a half-tree shadow for every base and every order. The trees
    at different bases share one tile family, so crossing is trivial. This recovers
    `cocompact-tree-end-shift-hosts-are-f-infinity`.
  - *`Z²` with its standard basis:* cone tiles are quadrant-type sets whose shape depends on the order. There
    is no finite shadow basis over an amenable group (one-scale node), so crossing must fail there. That is
    consistent with the grid control of the pentagon test.
- **Kazhdan inputs need a non-median spine (remark).**
  - Suppose the common refinements of descent trees had unique minimal elements given by a median join, as
    the Roller cylinders over walls do in `reflection-group-atoms-are-roller-cylinders-and-need-walls`.
  - Then the tiles would come from a proper action on a median graph.
  - An infinite Kazhdan group has no such action (a-T-menability is equivalent to a proper action on a median
    space; Chatterji–Druţu–Haglund, recalled).
  - So for Kazhdan `Γ`, the spine must be non-median: several minimal common refinements. That is Thumann's
    non-LCM regime, where condition (G) of `thumann-finiteness-without-finite-type` is the tool.
- **Seeds and rigidity do not enter this step.**
  - Rigidity (37abcc802) is the linear shadow of the filling and is already supplied.
  - The seed host maps onto the boundary host with a finitary kernel
    (`seed-full-groups-surject-onto-boundary-full-groups`). So seeds add nothing to the finiteness of the
    boundary host.

## Lesson for general BH

- **Canonical descent removes branching.** For a combing automaton, choose one downhill letter by a fixed
  order. Its cone tiles then certify their own upstream: every piece of a tile is a translate of a tile inside
  it, with finitely many types. This holds in every ShortLex-automatic group, so for all hyperbolic groups.
- **The finiteness gate sits between trees.** Once each tile's own splits are exact, all remaining finiteness
  lives between descent trees at different bases: square filling and a finite spine. Rigidity is the linear
  shadow of that filling. Walls (median joins) are the only known way to fill it.
- **For property (T) inputs the filling must be non-median.** Their hosts need Thumann's non-LCM machinery,
  meaning several minimal common refinements and highly connected splitting categories, and never a cube
  complex.

## Next

1. **Crossing test (needs one MSI job; ask the coordinator first).** Compute, for bases `1` and `s`, the
   common refinements of the two ShortLex descent trees to depth `n`, and count minimal common refinements
   per configuration type. Calibrate on the free group (unique, trivial) and `Z²` (unbounded). Run on the
   right-angled pentagon group (expected: median, cubical) and on a hyperbolic triangle group.
2. **Kazhdan building lattices (route, unproved).** For `Γ` acting cocompactly on a thick hyperbolic
   triangle building whose links are generalized quadrangles `GQ(q,q)`, `q ≥ 7`, `Γ` is hyperbolic and
   Kazhdan (Żuk / Ballmann–Świątkowski spectral criterion; recalled).
   - The `W`-valued version of item 1 holds, with lex-least left descents, by the building axiom
     `δ(x,z) = δ(x,y)δ(y,z)` whenever lengths add.
   - Crossing is then governed by projections to spherical residues, where minimal common refinements are the
     opposite chambers of a generalized quadrangle: several, as item 4 requires.
   - The splitting categories become joins of opposition complexes, which is where connectivity for (G) would
     come from. This is the most concrete candidate for a first `F_∞` host of a Kazhdan hyperbolic group.

## Crossing test (09-19, one direct run, 13 s)

`research/artifacts/gq-bh-finf-hyp-shortlex-crossing-test.md` compares ShortLex trees at adjacent bases.
- Every tile of one tree is a union of tiles of the other at most one level deeper (two, once, in the thin
  (4,4,4) group). The excess does not grow with depth.
- This holds in all five cases:
  - F2 (calibration);
  - Z² (control);
  - the right-angled pentagon group;
  - the (4,4,4) Coxeter group;
  - a thick (4,4,4) building with GQ(2,2) residues, grown to radius 9 with exact chamber counts and all
    self-checks passing.
- So square filling at adjacent bases shows no obstruction, thick or thin. But Z² also passes: its ShortLex
  boundary has isolated points, so the statistic is necessary and not sufficient.
- What remains for the Thumann route: the Cantor property of `∂Ω`, a finite spine or (G) for far bases, and
  `q ≥ 7`.
