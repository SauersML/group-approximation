---
rg: 2
id: coherent-variation-caps-review
kind: claim
title: Referee review of rigid-subshift-amenability-from-coherent-variation-caps (bh-ra-proof) — items 1–5 hold as stated; the cap-coherence criterion is a correct Reiter-function construction; repairs are the title's "clouds are rays" (they contain rays), the general-centre form of item 3 that item 4 uses, and marking the osculation paragraph heuristic
distinct_from:
  rigid-subshift-amenability-from-coherent-variation-caps: that is the lane node under review (last touched 847bcb5d7b); this checks it item by item and lists repairs.
  products-of-trees-refute-cap-coherence-join-caps-restore-it: that refutes (CC′) by an example; this checks the criterion (CC) ⇒ amenability itself, which that refutation leaves intact.
---

**ESTABLISHED (referee bh-ref-d, 2026-09-19; review of the lane node by bh-ra-proof).** Verdict:
**PASS with repairs.** No priority claimed. Nodes read at source on origin/main:
- `rigid-subshift-amenability-from-coherent-variation-caps` (as of 847bcb5d7b);
- `quantum-rigid-subshifts-cluster-the-modifications-of-each-point` (Lemma 1, clustering);
- `rigid-subshifts-over-free-factors-are-tight-almost-everywhere` (Lemma 1′);
- `fp-v-times-subshift-full-groups-force-quantum-rigidity` ((Q1)–(Q3));
- `wall-orientation-subshifts-are-quantum-rigid` (the coding of `R(Λ)`).

## Item by item

1. **Clouds.**
   - (a) PASS. Lemma 1′ needs two colourings whose `B_D`-patterns occur in `X` and whose difference
     set splits into two pieces at distance `> 2D`. Here both `x` and `y` lie in `X`, so the hypothesis
     is immediate.
   - (b) PASS. This is Lemma 1 of the clustering node verbatim.
   - (c) PASS. Non-isolation gives `y_r ≠ x` agreeing with `x` on `B_r`, so `Δ(x, y_r)` misses `B_r`,
     and clustering puts `Δ(x, y)` within `2D` of it. The `2D`-graph on `Δ(x, y)` is connected by (a),
     infinite and locally finite, so König's lemma gives a simple ray, which leaves every finite set.
2. **Finite windows.** PASS.
   - `ρ_r^1(x) ≥ s` iff the pattern `x|B_r` has a unique extension to `B_(s−1)` in `X`. That is a
     function of `x|B_r`.
   - Each value is finite. Every occurring pattern on `B_r` is the restriction of some point, which is
     not isolated, so its cylinder holds a second point differing at finite distance. The alphabet is
     finite, so there are finitely many patterns and `ρ̄(r) < ∞`.
   - The description of `V_r^1(x) ∩ B_M` by patterns `Q` on `B_M` checks in both directions.
3. **Equivariance.** PASS. With `B_r(c) = cB_r` (left-invariant metric), `y' = g.x` on `B_r` iff
   `g⁻¹.y' = x` on `B_r(g⁻¹)`, and `Δ(g.x, y') = gΔ(x, g⁻¹.y')`. The same computation gives the
   general-centre identity `Cap_r^a(g.x) = g·Cap_r^(g⁻¹a)(x)`, which item 4's proof uses
   (`ν_R^(cs)(x) = c_* ν_R^s(c⁻¹.x)`). **Repair:** state that form in item 3.
4. **Cap coherence ⇒ amenability.** PASS.
   - `m_R` is locally constant with uniformly finite support, hence continuous into `Prob(Λ)` with the
     `ℓ¹` norm.
   - The reduction from generators to all `g` is correct: centre-shift invariance of the sup, then the
     triangle inequality along a word for `g⁻¹`.
   - The resulting condition, `lim_R sup_x ‖g_* m_R(x) − m_R(g.x)‖_1 = 0` for every `g`, is the
     definition of a topologically amenable action by continuous approximately invariant means
     (recalled: Brown–Ozawa Def. 4.3.1). Exactness then follows (recalled: Brown–Ozawa Thm 5.1.7).
5. **Flippable walls.** PASS. In `R(Λ)` the symbol at `g` records the chosen side of each wall through
   an edge at `g`. Reversing one wall `w` therefore changes symbols exactly at the endpoints of the edges
   of `w`, so `Δ(x, y_i)` is that endpoint set, and clustering applies.

## Calibration and discussion

- **End shift of `F_n`.** PASS. `Δ(ξ, η)` is the line `(ξ, η)`. A line avoiding `B_r(c)` branches off
  `[c, ξ)` at some `p_k` with `k ≥ r+1`, so `ρ = r+1` and, with `L = 0`, `Cap_r^c = {p_(r+1)(c)}`. The
  two averaged measures are uniform on `R`-point segments sharing `R − 1` points, so their distance is
  `2/R`; the node's `≤ 4/R` is a correct, looser bound.
- **"Must fail" row.** PASS. An amenable action with an invariant probability measure forces the group
  to be amenable (recalled; integrate the means against the measure). Closed invariant subsets of a
  rigid subshift are rigid, since their (Q3) conditions include those of the ambient shift. So the
  perfect part inherits rigidity.
- **Consequences for BH.** Conditional on (RA′), and they rest on other nodes (the seed route via
  E1′+E2, and `ra-counterexamples-are-minimal-sets-of-rigid-ambients`). I did not re-check those nodes.
  The logical use is correct: every overgroup of a non-exact group is non-exact.
- **Osculation paragraph** ("flippable walls at `x` are the hyperplanes adjacent to `x` in its Roller
  component … in hyperbolic cube complexes osculation at infinity forces asymptotic walls"). This is
  unproved. **Repair:** mark it heuristic.

## Repairs

1. **Title.** "Modification clouds are coarsely connected rays" should read "modification supports are
   coarsely connected, unbounded, and contain coarse rays". Item 1(c) proves containment, not equality.
2. **Item 3.** Add the general-centre identity `Cap_r^a(g.x) = g·Cap_r^(g⁻¹a)(x)`.
3. **Discussion.** Mark the osculation paragraph heuristic.

## Priority

The construction is the standard Reiter-function route to topological amenability, applied to the
nearest variation points. The node credits Anantharaman-Delaroche–Renault, Ozawa, Higson–Roe and Yu,
and bh-star-b for the clustering and two-piece lemmas. That credit is correct. I know of no prior
statement of cap coherence. Since (CC′) is false (cf68fcdd7), the criterion's use is as a sufficient
condition at a given `X`, as the node already says.
