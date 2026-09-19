---
rg: 2
id: torsion-germ-rn-groups-are-not-k-graph-full-groups
kind: claim
title: If a finite-order element of a self-similar group H has a nontrivial germ at a fixed point, then V_d(H) is not the full group of any aperiodic finite k-graph, for any k; so the 2-graph method that settles the lamplighter fails for the Grigorchuk and Hanoi groups
distinct_from:
  rn-lamplighter-is-f-infinity-and-acyclic-via-a-2-graph: that realises one Roever-Nekrashevych group as a 2-graph full group; this proves that such realisations are impossible whenever a torsion element has a nontrivial fixed-point germ, and names the groups affected.
  ct-p-z-is-a-one-vertex-k-graph-full-group: that is a positive k-graph realisation of another group; this is an obstruction for Roever-Nekrashevych groups.
  li-finite-k-graph-full-groups-are-f-infinity: that is Li's finiteness theorem for k-graph full groups; this shows that the theorem cannot be applied directly to V_2(Grigorchuk) or V_3(Hanoi).
  contracting-rover-nekrashevych-groups-are-f-infinity: that asks whether V_d(G) is F_infinity for all contracting G; this rules out one route to it (k-graph models) for a named class, and does not decide the question.
  rover-nekrashevych-bounded-automata-sigma-invariants-full: that proves finiteness for bounded automata through the germ complex; this is an isomorphism-type obstruction and proves no finiteness.
  finite-k-graph-boundary-groupoid-standard-facts: that records the Hausdorff and effectiveness facts used here; this applies them, through Rubin's theorem, to Roever-Nekrashevych groups.
artifacts:
  - experiments/rn-lamplighter-finiteness-2026-09-17/fixed_germs.py
  - experiments/rn-lamplighter-finiteness-2026-09-17/results-fixed-germs.txt
  - experiments/rn-lamplighter-finiteness-2026-09-17/review_two_graph.py
  - experiments/rn-lamplighter-finiteness-2026-09-17/results-review-two-graph.txt
---

**ESTABLISHED (proof in `torsion-germ-rn-groups-are-not-k-graph-full-groups-proof`; lane proof, w11-101; not
independently reviewed).** Parts 1 and 2 are proved in full. They use only the definitions, the facts recorded in
`finite-k-graph-boundary-groupoid-standard-facts`, and Rubin's reconstruction theorem (imported). Part 3 is a
computation plus citations, and part 4 is a remark with no claim.

## Setting

- `H ≤ Aut(X^*)` is self-similar on the alphabet `X = {0, ..., d-1}`, with `d ≥ 2`. `V_d(H)` is its
  Röver–Nekrashevych group, acting on `X^ω`.
- `Λ` is a finite `k`-graph (for any `k ≥ 1`). It satisfies hypothesis **(H)**: it is aperiodic, and every vertex
  receives and emits at least two edges of each colour.
- `G_Λ` is its Kumjian–Pask path groupoid on `Λ^∞`, and `F(G_Λ)` is its topological full group.
- A germ of `h ∈ H` at a fixed point `ξ ∈ X^ω` is *nontrivial* if `h` is not the identity on any neighbourhood of `ξ`.
  Equivalently, every section `h|_{ξ_1...ξ_n}` is nontrivial.

## Statement

1. **Obstruction.** Suppose some `h ∈ H` of finite order has a nontrivial germ at a fixed point. Then there is no
   `k ≥ 1` and no finite `k`-graph `Λ` with (H) such that `V_d(H) ≅ F(G_Λ)` as abstract groups.
   - More generally, `V_d(H)` is not isomorphic to the topological full group of any effective, ample, Hausdorff
     groupoid with torsion-free isotropy on a Cantor set, whose full group acts in a locally moving way.
2. **A second obstruction.** Suppose the groupoid of germs of `V_d(H)` is not Hausdorff. That is, some `g ∈ H` has a
   nontrivial germ at a fixed point `ξ` that cannot be separated from the germ of `1`. Then again `V_d(H) ≇ F(G_Λ)`
   for every `Λ` with (H).
3. **The three test groups.** The criteria are decided by a finite computation on the nucleus (`fixed_germs.py`).
   The computation follows the fixing graph `g → g|_x` (for `g(x) = x`) of a section-closed set.

   | Group | Relevant germs | Verdict |
   |---|---|---|
   | **Grigorchuk** `a = σ`, `b = (a,c)`, `c = (a,d)`, `d = (1,b)` | `b` fixes `1^ω`, its sections along `1^ω` cycle through `b, c, d`, and `b² = 1`. Its germ at `1^ω` has order 2. The germs of `d` and of `1` at `1^ω` are inseparable, because `d` is the identity on the cylinders `1^{3m}0X^ω`, which accumulate at `1^ω`. So the germ groupoid is not Hausdorff. | Parts 1 and 2 both apply. **`V_2(Grigorchuk)` (Röver's group) is not a `k`-graph full group for any `k`.** |
   | **Hanoi towers** `H^(3)`: `a = (01)(1,1,a)`, `b = (02)(1,b,1)`, `c = (12)(c,1,1)` | `a` fixes `2^ω` with section `a` along it, and `a² = 1`. Similarly `b` at `1^ω` and `c` at `0^ω`. The germ groupoid is Hausdorff: no fixing-graph cycle reaches `1`. | Part 1 applies. **`V_3(H^(3))` is not a `k`-graph full group for any `k`.** |
   | **Basilica** `IMG(z²-1)`: `a = σ(1,b)`, `b = (1,a)` | The fixing graph of the section-closed set (153 elements, containing the nucleus of 7) has no cycle avoiding `1`. So every fixed-point germ of an element of `H` is trivial. The germ groupoid is Hausdorff, and the level cocycle embeds its isotropy in `Z`. | Neither obstruction applies. Whether `V_2(Basilica)` is a `k`-graph full group is **not decided** here (see part 4). |

   The adding machine is included in the run as a calibration: it has no fixed-point germs.

   **Finiteness is not affected.** All three groups are bounded automata groups, and their Röver–Nekrashevych
   groups are already of type `F_∞`:
   - `V_2(Grigorchuk)` by Belk–Matucci, *Röver's simple group is of type F_∞*, Publ. Mat. 60 (2016).
   - All three by Belk–Hyde–Matucci, arXiv:2407.03149, as recorded on main in
     `contracting-rover-nekrashevych-groups-are-f-infinity` (Attempts) and in
     `rover-nekrashevych-bounded-automata-sigma-invariants-full`.
   - Basilica also by `hyperbolic-pcf-rational-nekrashevych-groups-are-f-infinity`, since `z² - 1` is hyperbolic
     and post-critically finite.

   So the extension asked for in the target has a negative answer for Grigorchuk and Hanoi: the 2-graph (or
   `k`-graph) method gives nothing there. For those groups `F_∞` holds anyway, by other methods.
4. **Remark (not claimed): basilica and hyperbolicity.** For `k ≥ 2`, the proof gives a quasi-isometric embedding
   of `N^k` into the Cayley graph of `G_Λ` based at an aperiodic point. For a contracting `H`, Nekrashevych's
   groupoid of germs is hyperbolic (*Hyperbolic groupoids and duality*, Mem. AMS 2015; not read at source here).
   Together, these would exclude `𝒢_Basilica ≅ G_Λ` for `k ≥ 2`. Two steps are not done:
   - identifying `Germ(F(G_Λ))` with `G_Λ` in general;
   - the case `k = 1`.
   The lamplighter escapes this obstruction because `Z/2 ≀ Z` is not contracting, and its groupoid is
   `S`-arithmetic of rank 2 (`rn-lamplighter-is-a-function-field-stein-group`).

## Review of `rn-lamplighter-is-f-infinity-and-acyclic-via-a-2-graph`

The same lane reviewed that proof independently. The review found **no gap**. Lemma 2 (unique factorisation) and
the germ step were checked by hand, and every computation was recomputed by independent code
(`review_two_graph.py`, output `results-review-two-graph.txt`).

- The code decides membership in `P` from the valuation definition, not from the claimed normal form. It
  exhaustively checks the normal form for `d ≤ (3,3)`, the unique factorisation (2401 cases) and the germ threshold
  (`P_(M,M)` for `M ≤ 7`).
- Details, and two wording fixes, are in the proof file.
