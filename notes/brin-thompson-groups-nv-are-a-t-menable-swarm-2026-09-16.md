# Swarm lane: brin-thompson-groups-nv-are-a-t-menable (2026-09-16)

Target: `brin-thompson-groups-nv-are-a-t-menable`, the affirmative Haagerup side of
Zaremsky Problem 2.7. Hole worked: the target itself, locked with a 180m TTL.
Outcome: a reduction in both directions to one explicit group, `C(C,Z) ⋊ V`. This
is the case `Γ = Z` of Brothier's Problem B. Neither the target nor the reduced
problem is resolved.

## 1. Setup

- `C = {0,1}^N`; `nV` is the group of piecewise brick-canonical homeomorphisms of
  `C^n`.
- For a discrete group `Γ`, let `G_Γ = C(C,Γ) ⋊ V`, the locally constant maps
  `C → Γ` with `V` acting by precomposition.
- The main case is `G = C(C,Z) ⋊ V`, with `A = C(C,Z)`.

## 2. Literature gate (checked 2026-09-16)

Status: both sides of the Haagerup question for `nV`, `n ≥ 2`, are still open as
far as these searches show. Brothier's Problem B has no recorded resolution.

Sources:

- **arXiv API, `abs:"Brin-Thompson"`**, 40 newest, fetched 2026-09-16. Relevant
  entries:
  - 2603.24687 (Mar 2026), twisted Brin–Thompson groups.
  - 2603.18410v3 (Mar 2026), Kojima–Sheng on subgroups of `nV`.
  - 2602.18197, 2601.13279, 2506.02319, 2503.21882.
  - 2405.19923 (divergence functions of higher-dimensional Thompson groups).
  - 2403.02562 (grid diagrams).
  - 2208.00685v3, Callard–Salo, *Distortion element in the automorphism group of a
    full shift*: `2V` has a distorted element, so it admits no proper cubical
    action.

  None claims the Haagerup property or property (T) for `nV`.
- **arXiv API, `abs:"wreath products" AND abs:Haagerup`**, fetched 2026-09-16. Found
  1906.03789v3, Brothier, *Haagerup property for wreath products constructed with
  Thompson's groups*, published in GGD 2023. Its tex source was read.
  - Theorem A: `Γ ≀_{Q_2}^θ V` is a-T-menable if `Γ` is.
  - Problem B, verbatim: "Assume that Γ is a discrete group with the Haagerup
    property. Is is true that C(𝔊,Γ)⋊V has the Haagerup property?" Here
    `𝔊 = {0,1}^N` and `V` acts by the standard action.

  The other hits were 2504.00596, 2212.01993, 2010.03765 and 0905.3960
  (Cornulier–Stalder–Valette, *Proper actions of wreath products and
  generalizations*).
- **Semantic Scholar citations of arXiv:1906.03789**, fetched 2026-09-16, 13
  citing papers:
  - 2607.28406 (V and virtual links, 2026)
  - 2604.15883
  - 2510.02019
  - 2406.09718 (forest-skein groups III)
  - 2306.01256 and 2302.04458 (Pythagorean representations)
  - 2212.01993
  - 2211.08555
  - 2011.13124 (Brothier, *Classification of Thompson related groups arising from
    Jones' technology II*: the `C(C,Γ) ⋊ V` family; its abstract was fetched and
    does not mention Haagerup)

  No title suggests a resolution of Problem B. Only abstracts and titles were
  checked. The citation list may be incomplete.
- **arXiv:0804.0610**, Hughes, *Local similarities and the Haagerup property*
  (abstract fetched 2026-09-16). LFD groups of local similarities are a-T-menable.
  Farley's appendix shows that the sufficient condition used is equivalent to a
  proper action on a space with walls.
- **arXiv:2507.18821v2** (Bashwinger–DeBonis, May 2026), CSS* similarity structure
  groups. Its abstract has no Haagerup statement.
- Salo 2103.06663 (RAAGs in `2V`) was imported via
  `notes/zaremsky-2-19-embeddings-into-brin-thomp-swarm-2026-09-16.md`.
- Not re-read, cited from memory and unverified: Bleak–Bowman–Gordon–Graham–Hughes–
  Matucci–Sapir, *Centralizers in R. Thompson's group V_n*, for undistortion of
  cyclic subgroups of `V`. Chatterji–Niblo and Nica, for proper actions on spaces
  with walls giving proper actions on CAT(0) cube complexes.
- Later arXiv and Semantic Scholar queries in this session hit rate limits (HTTP
  "Rate exceeded" / 429), and the WebSearch budget was exhausted. A 2026 preprint
  on Problem B that is not in the citation index could have been missed.

## 3. What was proven

Full proofs are in `research/artifacts/cantor-maps-by-v-in-brin-thompson-2026-09-16.md`.

1. **Embedding lemma** (claim `cantor-maps-by-v-embed-in-next-brin-thompson-group`,
   with direct-proof route). For `Γ ≤ nV`,
   `Φ(f,h)(x,p) = (hx, f(hx)(p))` embeds `C(C,Γ) ⋊ V` in `(n+1)V`. In particular
   `C(C,Z) ⋊ V ≤ 2V` and `C(C,V) ⋊ V ≤ 2V`.
2. **Two reductions** (routes):
   - `cantor-integer-maps-haagerup-from-nv-a-t-menability`: the target implies the
     new open claim `cantor-integer-maps-by-v-have-haagerup-property`, Problem B for
     `Γ = Z`. So Problem B for `Z` is a necessary step for the target.
   - `brin-thompson-2v-not-a-t-menable-via-cantor-integer-maps`: the new open claim
     `cantor-integer-maps-by-v-are-not-a-t-menable` implies
     `brin-thompson-2v-is-not-a-t-menable`.
   - More generally, the target implies Problem B for every `Γ` embeddable in a
     Brin–Thompson group, including all subgroups of `V` and all RAAGs, via Salo.
     A counterexample to Problem B in that class refutes the target.
3. **Finite Γ.** `C(C,Γ) ⋊ V ≤ V_{2,|Γ|} ≅ V` by `(x,γ) ↦ (x, f(x)γ)`. This is
   already in the graph as the case `φ0 = φ1 = id` of
   `twisted-power-cloning-groups-embed-in-v`, so no new node was made. `Γ = Z` is
   the first open case.
4. **Structure of `G = C(C,Z) ⋊ V`** (artifact §3):
   - (a) `G` is generated by `V` together with `1_{[0]}`.
   - (b) `G` is perfect.
   - (c) `‖f‖_∞ ≤ |(f,h)|_S`, so `1_C` is central and undistorted, and nothing in
     `A` is distorted. Every infinite-order element is undistorted, modulo the
     recalled undistortion of cyclic subgroups of `V`.
   - (d) `G` is a-T-menable iff some cnd function on `G` is proper on `A`.
   - (e) `V`-invariant quadratic forms on `A` vanish, so `V`-invariant cnd
     functions on `A` are pure Lévy integrals.
   - (f) Relative (T) of `(G,A)` holds iff there are no `V`-almost-invariant (TV)
     probability measures on `Â∖{0}` tending to `δ_0`.
   - (g) Measures on characters with at most `m` atoms are never almost invariant,
     since that set is `V`-paradoxical.

Why this is a genuine reduction rather than a restatement:

- `G` is abelian-by-`V`, and a-T-menability of `G` is a question about invariant or
  almost-invariant measures on the explicit compact group `Â` of finitely additive
  `T`-valued measures on clopen sets.
- On the negative side, `(G, A)` relative (T) is a checkable dynamical condition
  that would refute the target. It replaces the unexplored "find an infinite
  Kazhdan subgroup in `2V`".
- On the positive side, any Haagerup proof for `2V` must in particular produce a
  cnd function growing along `n·1_{[0]}` in this subgroup, which no chart-type
  construction does (§4).

## 4. Approaches and exactly where each dies

All of these were attempts to build a cnd function on `G` proper on `A`, or to
refute one.

1. **Labeled Farley charts.** Charts `ι_w` labeled by an integer `n`, with
   `g·(ι_w, n) = (g∘ι_w, n + f(w'))` on deep charts. Dies because, for a fixed
   label set, `f = 1_{[w]}` changes the label on every chart below `[w]`, and there
   are infinitely many. Every choice of label set per chart breaks at shallow `w`.
2. **Decorations modulo constants** (`X × A/Z·1`, subset `S̃ = {(ι_w, [0])}`).
   Commensurated, with `|gS̃ Δ S̃|` bounded by the caret counts of `h` and `f`. Dies
   on properness: `ψ(n·1_{[0]}) = 1`, only the root chart changes.
3. **Graph half-spaces `H_φ = {(x,m) : m ≤ φ(x)}` in `C × Z`.** `G` permutes them
   simply transitively along `A`, but they give no finite wall count: the region
   `H_φ Δ H_ψ` is an uncountable clopen set with no `G`-invariant counting
   measure.
4. **Maharam-type weights `2^{-|w|}`.** Transverse divergence: prefix replacement
   `v → v'` rescales weights by `2^{|v|-|v'|}`, so the weighted count is not
   `V`-almost invariant. Compare the shape-condition failure recorded in the
   Attempts of `kazhdan-subgroups-of-brin-thompson-groups-are-finite`.
5. **Cylinder-average characters.** `χ_k(f) = θ·2^{-k}Σ_{|w|=k} f(w)`. The kernel
   contains `2^k·1_{[w]}`-type combinations and `V` does not fix the average, so
   there is no uniform bound under generators.
6. **Difference-of-averages and endpoint characters.**
   - `χ(f) = θ(f(x) - f(y))`, and averages of these over pairs.
   - `ψ(1_{[u]})` stays bounded as `u` varies, and the endpoint versions `f ↦ f(0^∞)`
     are not proper along `n·1_{[u]}` with `u` away from the endpoint.
7. **Brick charts of `2V` restricted to `G`.**
   - With `Γ = ⟨s⟩`, `Φ(1_{[1]})` is `g(x,y) = (x, s(y))` on `[1] × C` and the
     identity on `[0] × C`. For `s` the first-letter swap this is the element in
     the target's Attempts, but that `s` has order 2 (the `Γ = Z/2` case); for
     `Γ = Z` take `s` of infinite order, and the same break occurs.
   - It breaks every brick `[u] × C` with `u` below `[1]`, infinitely many.
   - Restricting to `G` does not help.
8. **Fibred charts `(E, ζ_x)`,** a clopen `E` with a locally constant chart-valued
   map. `G` acts on them, but every standard subset is broken on infinitely many
   `E` (all non-level sets of `f`), and the family `E = C` with pointwise standard
   `ζ` is broken on infinitely many `v(·)`.
9. **Trivial-`A` cocycles.** Cocycles of `V` pulled back vanish on `A`. Cocycles
   supported on `A` built from the regular representation of `V` on `ℓ²(V)` do
   not give `ℓ²` vectors: `f ↦ Σ_h ...` diverges, since `A` is not finitely
   supported over any `V`-orbit.
10. **`V`-invariant Lévy measures.**
    - The quadratic part vanishes (artifact §3(e)).
    - Counting measure on point characters `tδ_x` over an orbit, the wreath-product
      mechanism, gives `F(1_U) = ∞`.
    - Difference characters `t(δ_x - δ_y)` give `∞` for the same reason.
    - Haar measure on `Â` gives `1 - δ_{f,0}`, which is bounded.
11. **Product and Gaussian measures on `Â`.** White noise mod 1 with intensity
    `δ²m`.
    - `h_*m ≠ m` for some `h` (for every `m` giving a clopen finite positive mass,
      next bullet), and white noises with different intensities are mutually
      singular (Kakutani, sketched only), so not TV-almost invariant.
    - There is no `V`-invariant σ-finite measure `m` giving a clopen finite positive
      mass. If `h[0] = [00]` then `m([01]) = 0`, and transitivity kills every proper
      clopen.
12. **Sup-norm length.** Linear in `‖f‖_∞`, but `ℓ^∞`-type and not cnd.

On the negative side, only one piece was proven. Relative-(T) witnesses must avoid
boundedly-atomic characters, by paradoxicality (artifact §3(g)). Non-atomic almost
invariant measures were neither built nor excluded.

## 5. Obstruction remark: local similarity groups

This is a conditional remark, not a node, because two of its links are recalled
rather than verified.

- Hughes (arXiv:0804.0610, abstract fetched) proves that every locally finitely
  determined (LFD) group of local similarities of a compact ultrametric space is
  a-T-menable. The abstract, re-fetched 2026-09-16, says verbatim: "A sufficient
  condition, used in this paper, for the Haagerup property is shown in the appendix
  by D. S. Farley to be equivalent to the well-known property of having a proper
  action on a space with walls." The exact form of that condition was not read.
- Nica, and independently Chatterji–Niblo, turn a proper action on a space with
  walls into a proper action on a CAT(0) cube complex. This is recalled and
  unverified.
- Callard–Salo (arXiv:2208.00685v3) show that `2V` contains a distorted element,
  so `2V` has no proper cubical action.

Conditional conclusion: if Hughes's LFD proof indeed produces a proper action on a
discrete space with walls, which is what the abstract says, then `nV` (`n ≥ 2`) is
not isomorphic to an LFD local similarity group for any compact ultrametric space
and any similarity structure. So the Hughes theorem cannot prove the target in any
presentation, not just the standard one. This strengthens the last Attempts bullet
of the target, which only says brick maps are not similarities for the max metric.

Supporting check, independent of the recalled links: the baker's map
`(0x, y) ↦ (x, 0y)`, `(1x, y) ↦ (x, 1y)` (Brin's element of `2V`) scales the
`x`-coordinate by 2 and the `y`-coordinate by `1/2`. For every product ultrametric
of the form `max(d_1^a, d_2^b)` it is not a local similarity near any point. This
only addresses the obvious metrics. The conditional argument above covers all.

This remark does not refute the target. It only rules out one family of proofs, the
same way Callard–Salo rules out cubical ones.

## 6. What remains open

- **The target** `brin-thompson-groups-nv-are-a-t-menable`, and its negation
  `brin-thompson-2v-is-not-a-t-menable`: both open.
- **Problem B for `Γ = Z`**, in both directions:
  - `cantor-integer-maps-by-v-have-haagerup-property` is necessary for the target.
  - `cantor-integer-maps-by-v-are-not-a-t-menable` is sufficient for its negation.
- **Negative side, concretely.** Decide whether `V`-almost-invariant probability
  measures on `Â ∖ {0}` tending to `δ_0` exist.
  - Boundedly-atomic characters are excluded (artifact §3(g)).
  - The remaining cases are non-atomic characters, or characters with unboundedly
    many atoms whose number tends to infinity along the sequence.
  - A natural test case is random characters `χ(U) = Σ_{x ∈ P} t_x 1_U(x)`, with `P`
    a Poisson-type point set of intensity tending to infinity and small random
    phases `t_x`. The Kakutani singularity argument of §4.11 suggests these fail
    almost invariance too, but no proof was written.
- **Positive side, concretely.** Build a cnd function on `G` that grows along
  `n·1_{[0]}`. By §3(e), any `V`-invariant candidate is a Lévy integral over
  `Â ∖ {0}`. So the positive side needs a genuinely non-invariant construction, for
  example a cocycle combining Farley's charts for `V` with a non-invariant Lévy
  measure whose defect is controlled by carets.
- **Γ in between.** Problem B for `Γ = Z^2`, free groups and RAAGs. These are all
  implied by the target via Lemma 1 and Salo. A counterexample in this class would
  refute the target, but no candidate is known.
- **Graph shape.** `cantor-integer-maps-by-v-have-haagerup-property` is a detached
  lane top by design. It is a necessary condition for the target, not a sufficient
  one, so no honest route from a reachable claim ends at it. It is consumed only
  as the refuter of `cantor-integer-maps-by-v-are-not-a-t-menable`, which is
  reachable through `brin-thompson-2v-not-a-t-menable-via-cantor-integer-maps`.
- **Unverified links** used only in remarks: BBGGHMS undistortion in `V` (§3(c)),
  Chatterji–Niblo/Nica (§5). The routes do not depend on them.
