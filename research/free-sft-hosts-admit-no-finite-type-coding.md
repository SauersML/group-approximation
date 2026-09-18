---
rg: 2
id: free-sft-hosts-admit-no-finite-type-coding
kind: claim
title: A finite graph-directed coding of an ample groupoid forces a contracting loop, whose germ fixes a point with attracting dynamics, so V times a free transformation groupoid has no finite-type coding and free-form P2′ needs an infinite-type finiteness theorem
distinct_from:
  v-times-quantum-rigid-sft-full-groups-are-fp: that is gate E3 (P2′) itself, still OPEN; this shows that no finite-type engine can prove it for a free action, and so it kills that node's translation-finitely-coded lead in its graph-directed form.
  v-times-rigid-topologically-free-sft-full-groups-are-fp: that is E3′ for topologically free SFTs, which has proved finite-type instances; this explains why every proved instance is non-free, since finite type needs isotropy at attracting fixed points.
  finitely-coded-cantor-actions-give-type-a-hosts: that turns a finitely coded groupoid into a type (A) host; this shows that such a groupoid is never Kakutani equivalent to V times a free action, or to any product with a principal factor.
  free-group-boundary-shifts-are-quantum-rigid: that finds rigidity by compression in the non-free end shift; this shows that the non-freeness is forced, because finitely coded compression is contraction and contraction has fixed points.
---

**ESTABLISHED** (elementary lane proof, bh-g3-tfc, 2026-09-18; not reviewed; no priority claimed.
Isotropy at periodic points of Cuntz–Krieger and Nekrashevych groupoids is folklore. The new points
here are the product lemma (3) and the measure lemma (5), and what they mean for gate E3.)

## Setting

- `𝒢` is an ample groupoid on a Cantor space `Z`.
- A *bisection* means a compact open bisection. For a bisection `b` and `A ⊆ s(b)`, write `b(A)` for
  `r(bA)`.
- `C = {0,1}^N` is Cantor space, `G_V` is the groupoid of germs of prefix replacements on `C`, and `Λ`
  is a countable group acting on a Cantor space `X`.

**Definition (contracting loop).** A *contracting loop* is a bisection `b` with `s(b) = U` and
`b(U) ⊆ U`, such that `⋂_n b^n(U)` is a single point `p`.

**Definition (finite coding).** A *finite coding* of `𝒢` consists of:
- finitely many nonempty compact open sets `S_1, …, S_m ⊆ Z`;
- for each `t`, a partition `S_t = ⊔_j σ_{tj}(S_{τ(t,j)})` into at least two pieces, where each
  `σ_{tj}` is a bisection with source `S_{τ(t,j)}`;

such that the iterated pieces `σ_{t j_1} σ_{τ j_2} ⋯ (S_…)` along every path have diameters tending
to 0.

Every finite-type finiteness engine used on main runs on such a coding:
- **Li-coded groupoids** (`finitely-coded-cantor-actions-give-type-a-hosts`). Split `∂(w)` into the
  cylinders `μ∂(s(μ))` with `d(μ) = 𝟙 = (1,…,1)`, taken modulo units. These pieces are pairwise
  disjoint by (UFP*), finitely many, and they cover. The bisections are left multiplication by `μ`.
  The full-degree cylinders generate Li's topology, so their mesh tends to 0.
- **Stein–Farley / Brown complexes with finitely many cone types and a Garside family**:
  - `V` and `nV`;
  - Witzel's Ore categories with Garside families;
  - the Röver–Nekrashevych groups `V_d(G)` of Skipper–Witzel–Zaremsky.

  Here the Garside expansion `Δ` of each cone type is the partition, and the canonical similarities
  are the `σ`. Cofinality of `Δ`-expansions is exactly the mesh condition.

## Statement

1. **Contracting loops fix points, with nontrivial germs.**
   - If `b` is a contracting loop with limit point `p`, then `b(p) = p`.
   - The germ `[b, p]` is a nontrivial element of the isotropy group `𝒢_p^p`. Otherwise `b` would be
     the identity on a neighbourhood `W` of `p`, so `b^n(W) = W` for every `n`, and `W` is not a
     point.
2. **Finite codings produce contracting loops.**
   - The coding graph is finite, so it has a cycle `t_0 → t_1 → ⋯ → t_k = t_0`.
   - Let `b = σ_{t_0 j_0} σ_{t_1 j_1} ⋯ σ_{t_{k-1} j_{k-1}}`. It has source `S_{t_0}` and
     `b(S_{t_0}) ⊆ S_{t_0}`.
   - `b^n(S_{t_0})` is the piece of depth `nk` along the periodic path, so the pieces shrink to a point.
   - Having a contracting loop is invariant under Kakutani equivalence (see the proof).
3. **Product lemma.** Let `𝒢 = G_V × (Λ ⋉ X)`, and let `b` be a contracting loop with limit point
   `p = (c, x)`. Then the `Λ`-label `λ` of the germ `[b, p]` satisfies:
   - `λ ≠ 1` and `λx = x`;
   - `x` is an **attracting** fixed point of `λ`: there is a clopen `W ∋ x` with `λ^n W → {x}` in
     the Hausdorff metric.

   The same holds, with the same proof, for `ℋ × 𝒫`, where `ℋ` is any ample groupoid and `𝒫` any
   ample groupoid whose unit space has no isolated points. The conclusion there is that the
   `𝒫`-component of the germ is not a unit.
4. **Corollaries of (1)–(3).**
   - **(a) Free actions.** If `Λ` acts freely on `X`, then `G_V × (Λ ⋉ X)` has no contracting loop.
     So it has no finite coding, and neither does any groupoid Kakutani equivalent to it. The same
     goes for `ℋ × 𝒫` with `𝒫` principal. In particular `G_V × (Λ ⋉ X)` is never Li finitely coded,
     and `F(G_V × (Λ ⋉ X))` admits no finite-type Garside Stein–Farley complex. This holds whatever
     `Λ` is (amenable or not), whether or not `X` is rigid, and whether or not it is an SFT.
   - **(b) Where the isotropy lives.** If `G_V × (Λ ⋉ X)` has a finite coding (`X` minimal and
     infinite), then some `λ ∈ Λ` has an attracting fixed point in `X`, and no such `λ` is central
     in `Λ`.
5. **Measure lemma (flexible finite type, X-rigid similarities).**
   - *X-rigid bisections.* Call a bisection of `G_V × (Λ ⋉ X)` *X-rigid* if its source splits into
     finitely many sets `s(σ) ∩ ([v] × X)`, and on each of them `σ(c, x) = (φ(c), λx)` for one
     prefix replacement `φ` and one `λ`. The canonical similarities (prefix replacement times a
     translation) of Attempt 1 of `v-times-quantum-rigid-sft-full-groups-are-fp` are of this kind.
   - *Hypothesis.* `X` is minimal, `𝒮` is a finite family of compact open subsets of `C × X`, and
     `Σ` is a set of X-rigid bisections such that the sets `σ(S)` (for `S ∈ 𝒮`, `σ ∈ Σ`,
     `S ⊆ s(σ)`) form a basis of the topology.
   - *Conclusion.* No infinite factor of `X` carries a `Λ`-invariant probability measure.
   - A finite-type Stein–Farley complex needs exactly this basis property, since cofinality is what
     makes the vertex poset directed. So translation-finitely-coded SFTs have no infinite factor with
     an invariant measure, even without a Garside family.

## Proof

**(1)** We have `b(p) ∈ b(⋂ b^n U) ⊆ ⋂ b^{n+1} U = {p}`. Nontriviality is as stated above.

**(2) Kakutani invariance.**
- Suppose `𝒢|_U ≅ 𝒢'|_{U'}` with `U'` full, and `b'` is a contracting loop of `𝒢'` with limit point
  `p'`.
- Fullness gives a bisection `a` with `p' ∈ s(a)` and `r(a) ⊆ U'`.
- For large `n`, `A := b'^n(s(b')) ⊆ s(a)`. Then `a · b'|_A · a^{-1}` is a contracting loop inside
  `U'`, with limit point `a(p')`.
- It transports to `𝒢|_U ⊆ 𝒢`.

**(3)**
- Basic open sets of `G_V × (Λ ⋉ X)` have the form `O × ({λ} × W)`, where `O` is a bisection of
  `G_V` and `W ⊆ X` is clopen.
- The germ `[b, p]` is `(η, (λ, x))` with `λx = x`. Since `b` is open, it contains a basic set
  `O' × ({λ} × W')` through the germ.
- So on the neighbourhood `N = s(O') × W'` of `p`, `b(c', x') = (φ(c'), λx')`.
- The sets `b^n(U)` are compact and decrease to `{p}`, so `b^n(U) ⊆ N` for `n ≥ n_0`.
- For those `n`, `π_X(b^{n+1}U) = λ π_X(b^n U)`, where `π_X` is the projection to `X`. So
  `π_X(b^{n_0+m} U) = λ^m E` with `E := π_X(b^{n_0} U)`, an open neighbourhood of `x`.
- **These sets tend to `{x}`.** For any neighbourhood `M` of `x`, eventually
  `b^n(U) ⊆ C × M`, so `λ^m E ⊆ M` for large `m`.
- **So `λ ≠ 1`.** Otherwise `E = {x}` would be open, and `x` isolated.
- Take `W ⊆ E` clopen with `x ∈ W`. Then `λ^m W → {x}`.
- For `ℋ × 𝒫`, replace `{λ} × W'` by a bisection of `𝒫` through the `𝒫`-component of the germ. If
  that component is a unit, the unit space is open, so `b` acts as `(ℋ-map) × id` near `p`. Then
  `E = {x}` again, a contradiction.

**(4a)** `λ ≠ 1` with `λx = x` contradicts freeness. For principal `𝒫`, every isotropy germ is a unit,
which (3) excludes.

**(4b)**
- Suppose `λ` is central, and `λ^n W → {x}`.
- Every `gx` with `g ∈ Λ` is fixed by `λ`.
- The orbit `Λx` is dense and `x` is not isolated, so some `gx ≠ x` lies in `W`.
- Then `gx = λ^n(gx) ∈ λ^n W → {x}`, so `gx = x`, a contradiction.

**(5)**
- Let `π : X → Y` be a factor map and `μ` an invariant probability measure on `Y`.
- **Lower bound on piece measures.**
  - Write each `S ∈ 𝒮` as a finite disjoint union of products `[u_i] × U_i` with `U_i` clopen and
    nonempty.
  - By minimality, finitely many translates of `U_i` cover `X`. So `μ(π U_i) ≥ 1/N_i`.
  - Let `c > 0` be the minimum of these bounds over all `S` and `i`.
  - If `σ ∈ Σ` and `S ⊆ s(σ)`, pick one of the finitely many pieces of `s(σ)` on which `σ` is
    `φ × λ`, and some `[u_i] × U_i` meeting it. Then `π p_X(σ S) ⊇ λ π(U_i)`, so its measure is at
    least `c`.
- **Every point is a heavy atom.**
  - Given `y = π(x)`, the basis property gives pieces `σ(S) ⊆ C × B(x, δ)` for every `δ`.
  - By uniform continuity of `π`, `μ(B̄(y, ε)) ≥ c` for every `ε > 0`, so `μ{y} ≥ c`.
- So `|Y| ≤ 1/c`. ∎

## Consequences for gate E3 (P2′) and the master route

- **The translation-finitely-coded lead is dead for free X.** Attempt 1 hoped that "compression
  supplied by Λ itself" would restore finite type over non-amenable `Λ`.
  - In graph-directed (Garside) form, compression is a contracting loop, and by (3) its fixed point
    is a non-free point.
  - In flexible form, (5) still forbids every infinite invariant-measure factor.
  - Paradoxicality (`f2-groups-have-paradoxical-free-minimal-subshifts`) gives `hK ⊊ K`, but not a
    coding. The attractor `⋂ h^n K` of a free action is never a point.
- **Free-form P2′ is an infinite-type theorem.** For free `X`, whatever `Λ`, rigidity or SFT, no
  proof of P2′ can use any of the following, because each of them runs on a finite coding:
  - Stein–Farley complexes with finitely many cone types;
  - Li's Garside finiteness theorem;
  - Witzel's Ore–Garside theorem;
  - the Skipper–Witzel–Zaremsky theorem.

  The only live set-up is Attempt 1's domain filtration `𝔓^{(N)}`, which is not cocompact, with its
  uniform connectivity (A_N). This includes the calibration case, ABHT's minimal free SFT over
  `F_n × Z`.
- **Why every proved instance on main is non-free.** The proved group-side instances are the
  tree-boundary scaffold `v-times-tree-boundary-full-groups-are-f-infinity`, Ã₂ lattices, Euclidean
  buildings and the end shifts. All of them are finitely coded, so all of them carry attracting
  fixed points of non-central elements.

  So bh-g2-fixedpoint-b's "the gap is FREENESS" is a theorem, not an accident of boundaries. Cheap
  rigidity and cheap finite type both come from contracting loops.
- **Recommendation.** Make E3′ (`v-times-rigid-topologically-free-sft-full-groups-are-fp`) the
  primary E3. bh-g3-topfree showed that the group side never uses freeness. There, finite type is
  available, and the open content moves to E1′/E2 with two explicit design constraints:
  - `Λ` must contain non-central elements with attracting fixed points in `X`, densely placed;
  - `X` must have no infinite factor with an invariant measure.

  So no fibre factor with an invariant measure is allowed (no Z²/odometer fibre), and pure
  product-with-centre constructions are excluded unless the compressing elements are off-centre.
  bh-g3-libridge adds that finite-state units cap the word problem, so complexity must sit in the
  unit groups.
- **What stays open.**
  - An infinite-type engine for free `X`: prove (A_N) for one free, rigid, minimal SFT.
  - The flexible residue of (5): finitely many X-rigid cone types without a Garside family, over a
    free action with no invariant-measure factor. No engine on main or in the cited literature
    handles this case.

**Lesson for general BH.** Finitely coded compression is contraction, and contraction has fixed
points. A finite-type finiteness engine exists only where the groupoid has isotropy with attracting
dynamics in the acting-group coordinate. So "free SFT" and "finite-type P2′" in the master route are
mutually exclusive. Either the route keeps freeness and must invent an infinite-type
(non-cocompact) Brown criterion, or it drops freeness for topological freeness (E3′) and inherits
Li's theorem. In that second case, the whole problem is to build a rigid, minimal, effective,
finitely coded host over `Λ ⊇ G` whose compressing elements are non-central and whose complexity
sits in the unit groups.
