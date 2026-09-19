---
rg: 2
id: rigid-subshift-amenability-from-coherent-variation-caps
kind: claim
title: A quantum-rigid subshift without isolated points has continuous, finitely supported variation caps whose modification clouds are coarsely connected rays; if the scale-averaged caps are asymptotically independent of the centre (cap coherence), the action is topologically amenable — the finite-window form of (RA), plus a flippable-wall test for the wall-orientation case
distinct_from:
  quantum-rigid-minimal-topfree-subshift-actions-are-amenable: that is the open question (RA)/(RA′); this reduces (RA) for a given X to one finite-window combinatorial property (cap coherence) and proves the reduction, without settling (RA′).
  rigid-subshifts-without-isolated-points-factor-onto-the-ends: that builds a continuous map to Ends(Λ) from finite cuts, which says nothing over one-ended groups; this builds Reiter functions directly from the nearest variation points, over any group, at the price of a coherence hypothesis.
  wall-orientation-subshifts-are-quantum-rigid: that poses the decisive test R(Λ); this adds a necessary condition for it (flippable walls at every boundary point must be 2D-close) and explains why cap coherence must fail there if (RA′) is false.
---

**ESTABLISHED** for items 1–5 (lane proof, elementary; bh-ra-proof, 2026-09-18; not reviewed; no
priority claimed). The standard facts marked "recalled" were not re-read. (RA) and (RA′) themselves are
**not** settled here.

## Setting

- `Λ` is finitely generated, with a finite symmetric generating set, word length `|·|`, left-invariant
  metric `d(a,b) = |a⁻¹b|` and balls `B_r(c)`; write `B_r = B_r(1)`.
- `X ⊆ A^Λ` is a subshift (finite type not assumed), `D`-quantum rigid over some field in the sense of
  (Q1)–(Q3) of `fp-v-times-subshift-full-groups-force-quantum-rigidity`, and **without isolated
  points**. The action is `(g.x)(h) = x(g⁻¹h)`, and `Δ(x,y) = {q : x(q) ≠ y(q)}`.
- **Variation at centre `c`, scale `r`.** `V_r^c(x) = ⋃ { Δ(x,y) : y ∈ X, y = x on B_r(c) }`.
  It is nonempty, since `x` is not isolated, and it misses `B_r(c)`.
- **First-variation radius.** `ρ_r^c(x) = min { d(c,p) : p ∈ V_r^c(x) }` (so `ρ_r^c > r`).
- **Caps.** Fix `L ≥ 0`. `Cap_r^c(x) = V_r^c(x) ∩ B_(ρ_r^c(x)+L)(c)`, a nonempty finite set.
- **Averaged cap measures.** `ν_R^c(x) = (1/R) Σ_(r=R)^(2R−1) u(Cap_r^c(x))`, where `u(F)` is the
  uniform probability measure on a finite set `F`. Write `ν_R = ν_R^1`.

## Theorem

1. **Clouds (from rigidity alone).** For every `x ∈ X`:
   - (a) every modification support `Δ(x,y)`, `y ≠ x`, is `2D`-coarsely connected;
   - (b) any two modification supports are `2D`-close (the clustering theorem);
   - (c) every modification support is unbounded and contains a `2D`-coarse ray, i.e. distinct
     points `p_0, p_1, …` with `d(p_i, p_(i+1)) ≤ 2D`, leaving every finite set.
2. **Caps are finite-window data.** `ρ_r^1(x)` depends only on `x|B_r`, so it is locally constant and
   takes finitely many values; put `ρ̄(r) = max_x ρ_r^1(x) < ∞`. `Cap_r^1(x)` depends only on
   `x|B_(ρ̄(r)+L)`. Hence `x ↦ ν_R(x)` is locally constant, with support in the fixed finite ball
   `B_(max_(r<2R) ρ̄(r) + L)`.
3. **Equivariance.** `Cap_r^1(g.x) = g · Cap_r^(g⁻¹)(x)`, so `ν_R(g.x) = g_* ν_R^(g⁻¹)(x)` and
   `‖ g_* ν_R(x) − ν_R(g.x) ‖_1 = ‖ ν_R^1(x) − ν_R^(g⁻¹)(x) ‖_1`.
4. **Cap-coherence criterion.** Suppose **(CC)**: for every generator `s`,
   `lim_(R→∞) sup_(x ∈ X) ‖ ν_R^1(x) − ν_R^s(x) ‖_1 = 0`.
   Then `Λ ↷ X` is topologically amenable. So `Λ` is exact (recalled: a group with a topologically
   amenable action on a nonempty compact space is exact; Ozawa, Anantharaman-Delaroche, see
   Brown–Ozawa §5.1 and §4.3).
5. **Flippable walls (for `wall-orientation-subshifts-are-quantum-rigid`).** In the wall-orientation
   subshift `R(Λ)`, call a wall `w` *flippable at `x`* if reversing the orientation of `w` alone gives
   another point of `R(Λ)`. If `R(Λ)` is `D`-quantum rigid, then at every `x ∈ R(Λ)` any two flippable
   walls are `2D`-close (as edge sets of the Cayley graph).

## Proof

1. (a) If `Δ(x,y) = Δ' ⊔ Δ''` with both parts nonempty and `d(Δ',Δ'') > 2D`, apply Lemma 1′ (the
   two-piece certificate) of `rigid-subshifts-over-free-factors-are-tight-almost-everywhere` to `x`
   and `z = y`. Both lie in `X`, so all their `B_D`-patterns occur in `X`, and rigidity fails.
   (b) is Lemma 1 of `quantum-rigid-subshifts-cluster-the-modifications-of-each-point`.
   (c) Fix `y ≠ x` and `r`. Since `x` is not isolated, some `y_r ∈ X ∖ {x}` agrees with `x` on `B_r`,
   so `Δ(x,y_r) ⊆ Λ ∖ B_r`. By (b), `Δ(x,y)` meets `Λ ∖ B_(r−2D)`. So `Δ(x,y)` is unbounded. By (a)
   its `2D`-graph is connected; it is locally finite and infinite, so König's lemma gives an infinite
   simple path. A simple path in a locally finite graph visits each vertex once, so it leaves every
   finite set for good.
2. `ρ_r^1(x) ≥ s` holds iff every `y ∈ X` with `y = x` on `B_r` also has `y = x` on `B_(s−1)`, i.e. iff
   the pattern `x|B_r` has exactly one extension to `B_(s−1)` occurring in `X`. That depends only on
   `x|B_r`. There are finitely many such patterns, and each has a finite value, because `X` has no
   isolated points. Next, `V_r^1(x) ∩ B_M` is the union of `Δ(Q, x|B_M)` over the patterns `Q` on `B_M`
   occurring in `X` with `Q = x` on `B_r`. That depends only on `x|B_M`. Take `M = ρ̄(r)+L`.
3. `y'` agrees with `g.x` on `B_r` iff `g⁻¹.y'` agrees with `x` on `g⁻¹B_r = B_r(g⁻¹)`. Also
   `Δ(g.x, y') = g Δ(x, g⁻¹.y')`. So `V_r^1(g.x) = g V_r^(g⁻¹)(x)`, `ρ_r^1(g.x) = ρ_r^(g⁻¹)(x)`, and
   the caps correspond. Push-forward by `g` is an `ℓ¹`-isometry.
4. By items 2–3, the maps `m_R : x ↦ ν_R(x)` are continuous into `Prob(Λ)` (they are locally constant
   with finite support). They satisfy `sup_x ‖g_* m_R(x) − m_R(g.x)‖_1 = sup_x ‖ν_R^1(x) −
   ν_R^(g⁻¹)(x)‖_1`.
   - For `g = cs`, write `ν_R^(cs)(x) = c_* ν_R^s(c⁻¹.x)` and `ν_R^c(x) = c_* ν_R^1(c⁻¹.x)`, both by
     item 3. So `sup_x ‖ν_R^c − ν_R^(cs)‖ = sup_x ‖ν_R^1 − ν_R^s‖`.
   - By the triangle inequality along a word for `g⁻¹`, (CC) for generators gives
     `sup_x ‖g_* m_R(x) − m_R(g.x)‖_1 → 0` for every `g`.
   - That is the approximately invariant continuous means condition, which is topological amenability
     (recalled; Anantharaman-Delaroche–Renault; Brown–Ozawa Def. 4.3.1).
5. If `w_1, w_2` are flippable at `x`, let `y_i` be `x` with `w_i` reversed. Then `y_i ∈ R(Λ) ∖ {x}`,
   and `Δ(x, y_i)` is the set of endpoints of the edges of `w_i`. By item 1(b) they are `2D`-close. ∎

## Calibration

| Subshift | Caps | (CC) | Consistent with |
|---|---|---|---|
| end shift of `F_n` | a point `ξ` has `Δ(ξ,η)` = the line `(ξ,η)`; `V_r^c(ξ)` is everything beyond the vertex `p_(r+1)(c)` at distance `r+1` on `[c,ξ)`; `ρ = r+1`; with `L = 0`, `Cap_r^c = {p_(r+1)(c)}` | holds: `ν_R^c` is uniform on the segment of `[c,ξ)` at distances `R+1 … 2R`; for a generator `s` the rays `[1,ξ)` and `[s,ξ)` merge within one step, so `‖ν_R^1 − ν_R^s‖ ≤ 4/R` | (RA) over `F_n` (`rigid-subshifts-over-free-factors-are-tight-almost-everywhere`, item 4) |
| `∂T_m ⊠ ∂T_n`, BMW and tree-product transplants | caps are products of ray points, up to bounded error in the fibre | **fails** for the product, at every point and every `L` (bh-star-b, `products-of-trees-refute-cap-coherence-join-caps-restore-it`, cf68fcdd7); 2-fold join caps cohere there. The first landing's "expected" was wrong | amenable boundary actions |
| Ã₂ boundary skew shift | caps are arcs of sectors toward `ω` (bh-star-b's reading, 9180ac550) | expected, since adjacent arcs are bounded translates; not checked | building boundaries are amenable (recalled) |
| any rigid `X` without isolated points carrying an invariant probability measure over a non-amenable `Λ` (for example Cornulier-regime coset shifts, 696c37d57, on their perfect part) | — | **must fail**, by item 4: an amenable action with an invariant probability measure forces `Λ` amenable (recalled) | rigidity plus topological freeness does not give (CC); minimality would have to |
| crossing-wire Z² (49939b957), and every rigid shift over an amenable group | — | irrelevant: the action is amenable because the group is | — |

Every rigid example on main therefore sits on the amenable side of item 4. That includes the
hyperbolic seed SFTs (b17ce0c51) and the cubulated Roller SFTs (807e18d5d). These are not minimal:
their seed orbits are isolated and dense, and their perfect parts factor onto the Gromov boundary and
the Roller boundary respectively. Those boundary actions are amenable (recalled: Adams; and
finite-dimensional cube complexes via Brodzki–Campbell–Guentner–Niblo–Wright).

## What this says about (RA) and (RA′)

- **Reduction.** For a given rigid `X` without isolated points, (RA) at `X` follows from (CC), a
  statement about the finite follower sets of `X`. So (RA′) follows from:

  > *(CC′) every minimal, topologically free, quantum-rigid subshift satisfies cap coherence.*

  **(CC′) is false** (`products-of-trees-refute-cap-coherence-join-caps-restore-it`, cf68fcdd7): the product
  `∂T_m ⊠ ∂T_n` is minimal, topologically free, rigid and amenable, and violates (CC). The reduction
  above is therefore void. The corrected target is bh-star-b's (JC′), *k*-fold join-cap coherence for some *k*,
  which implies amenability by the argument of item 4.
- **Why rigidity alone does not give (CC).** Item 1 is everything the known rigidity certificates yield.
  The certificates are the two-configuration wall families. They make the cloud of each point a
  pairwise-`2D`-close family of coarsely connected rays. (CC) asks for more: that the nearest variation
  points seen from adjacent centres coincide in proportion `1 − o(1)` of the scales. That is a
  fellow-travel property of the rays, and pairwise closeness does not imply it. The Cornulier regime
  shows the gap is real, since it is rigid and fails (CC).
- **Where minimality must enter.** Any proof of (CC′) has to use minimality, and in fact uniform
  recurrence of the follower sets. It must also use quantum families beyond two configurations. A
  Borel end map (as over `Λ_0 × F_n`) cannot replace (CC): slab data is infinite, and only finite
  windows give continuity. Continuity is what exactness needs.
- **For the decisive test `R(Λ)`** (Arzhantseva–Osajda-type walls):
  - if `R(Λ)` has a boundary point with two flippable walls far apart, then it is not rigid (item 5),
    and the test is killed cheaply;
  - if `R(Λ)` is rigid over a non-exact group, then its minimal sets violate (CC) and falsify (RA′).
  - Flippable walls at `x` are the hyperplanes adjacent to `x` in its Roller component. Two of them
    are far apart only if they osculate at `x` without coming close in `Λ`. In hyperbolic cube complexes
    osculation at infinity forces asymptotic walls, which are close. For infinite-dimensional
    small-cancellation walls this is unchecked, and it is the first thing to test.

## If (RA) (or just (RA′)) holds: consequences for BH

> **Scope (2026-09-19).** (RA) as stated is **refuted** on main by a non-free example with a
> non-amenable point stabilizer (`rigid-minimal-topfree-sft-with-non-amenable-point-stabilizer`; the group
> there is exact). What survives is
> - (RA′): a minimal, topologically free, rigid subshift forces an exact group;
> - (RA_free): a free, minimal, rigid subshift action is amenable.
>
> Read "(RA)" below as one of these, as stated at each use.

The consequences below need only (RA′) at `G`.

Take `G` from `decidable-residually-finite-non-exact-group-exists`. Every `Λ ⊇ G` is non-exact
(exactness passes to subgroups, recalled), so no `Λ ⊇ G` has any topologically amenable action.
- **Minimal-subshift group route (Track A) and its CARRIER.** No minimal, topologically free, rigid SFT exists over an
  fp overgroup of `G`. So the carrier (v7, a85dd1c95) fails at `G`.
- **Ring route (FJ ∧ Khanh).** v7 records `BH ⇐ CARRIER ∧ ((A₂) ∨ (FJ ∧ Khanh))`, so the ring route
  also starts from the carrier, and it fails at `G` too.
- **Seed routes.** A rigid seed over `Λ_0 ⊇ G` gives E1′+E2 over `Λ_0 ∗ Z`, which is a minimal,
  topologically free, rigid SFT over an overgroup of `G`. Such a seed therefore cannot exist.
- **Track B** is confined by a different mechanism (the Kirchberg shadow of linear gate U, 926454737).
  **Stabilizer engines** are dead (a23f54860).
- **The permutational route survives.** The route from a type (A) action to a twisted Brin–Thompson
  group is not obstructed. Its rigid coset ambients are topologically free and non-amenable, but they
  are never minimal (`ra-counterexamples-are-minimal-sets-of-rigid-ambients`, 4ed22df890, item 5).
  (RA) says nothing about them.
- **Net effect (corrected; the first landing overstated it).** The minimal-subshift tracks fail at `G`:
  the Track A carrier, the ring route and the seeds. The permutational route survives. So (RA′) does
  not force a new construction principle for BH; it moves the non-exact inputs onto the permutational
  route. BH itself is untouched: (RA) is a statement about our tools, not about BH.
- **Finite fibres** (`quantum-rigid-subshifts-are-determined-by-thick-collars`, item 5). Over the
  equicontinuous factor, finite fibres carry an invariant measure, so (CC) there forces the group to be
  amenable. Join-cap coherence (JC′) is the target only in infinite fibres; (CC′) itself is false (cf68fcdd7).
- **If (RA′) fails**, a counterexample is a minimal, topologically free, rigid subshift whose caps never
  cohere. The cheapest candidate is a minimal set of `R(Λ)` for a non-exact Haagerup group with walls.

## Lesson for general BH

**Amenability of a rigid action is a finite-window statement about where its first variations sit.**
- Rigidity gives every point a cloud of modification supports: coarsely connected rays, all pairwise
  close.
- Reiter functions come from the nearest points of the clouds (caps), averaged over scales. They work
  exactly when the caps seen from nearby centres agree (cap coherence).
- Trees and buildings cohere; measure-preserving rigid shifts over non-amenable groups cannot.
- So (RA′) is the question whether minimality plus higher-order quantum rigidity forces the clouds to
  fellow-travel. A non-exact group's expander geometry would have to break the route at exactly that
  point: first variations that disagree from nearby centres.

Credit: the Reiter-function characterisation of topological amenability is due to Anantharaman-Delaroche
and Renault; the equivalence of exactness with amenable actions is due to Ozawa and Higson–Roe; property
A is due to Yu. The clustering and two-piece lemmas, the ends reduction and the wall-orientation test are
bh-star-b's (ca15e5298, f676c07d2, 6a95ce886, 9180ac550).
