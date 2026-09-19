---
rg: 2
id: ball-helly-graphs-do-not-give-the-horofunction-lemma
kind: claim
title: The Helly property for balls never gives the exact realization the horofunction lemma (HL) needs, and coarsely gains at most a factor 2; the median and surface proofs used Helly for exact-distance cells (halfspaces), which Helly graphs lack, so Helly-ness of hyperbolic groups and C̃_n lattices does not give HL
---

**ESTABLISHED** (lane proof, bh-invent-13, 2026-09-18; elementary; not reviewed). This answers, in the negative, the
proposal "HL for all hyperbolic groups via Helly graphs". The question itself (HL for Helly graphs) stays OPEN.

## Source check (read in the arXiv PDF)

J. Chalopin, V. Chepoi, A. Genevois, H. Hirai, D. Osajda, "Helly groups", arXiv:2002.06895v3 (5 July 2023).
- **Def. 2.22.** A group is *Helly* if it acts geometrically (properly and cocompactly, not necessarily freely) on a
  Helly complex, i.e. on the clique complex of a Helly graph.
- **Theorem 1.1.** The following are Helly:
  1. groups acting geometrically on graphs with "near" injective metric hulls, in particular all hyperbolic groups;
  2. CAT(0) cubical groups;
  3. finitely presented graphical C(4)–T(4) small cancellation groups;
  4. groups acting geometrically on swm-graphs, in particular type-preserving uniform lattices in Euclidean buildings
     of type `C_n`.
- **Scope.** Ã₂ lattices are not covered by 1.1(4), which is type `C_n` only.
- **Theorem 1.2.** Coarse Helly plus β-stable intervals implies Helly. The paper relates β-stability to Cannon's finitely
  many cone types.

## 1. What ball-Helly buys: at most a factor 2 over the triangle inequality

Let `G` be any connected graph, `f` 1-Lipschitz with a descending (geodesic) path from each point, `A` finite, and `C`
large. HL on `A` asks for a vertex `q` with `d(x,q) = f(x) + C` for every `x ∈ A`.

- **Upper half.** `⋂_{x∈A} B(x, f(x)+C)` contains every point of `A` once `C ≥ diam A − min_A f`. So it is nonempty in
  every graph, with no Helly property needed.
- **Adding depth.**
  - Add points `y_x` at level `f = −C + r` on descending paths from each `x ∈ A`. Let `s` be the diameter of
    `{y_x : x ∈ A}`.
  - The balls `B(y_x, r)`, together with the `B(x, f(x)+C)`, pairwise intersect exactly when `s ≤ 2r`. A Helly point
    `q` then satisfies `f(x) + C − 2r ≤ d(x,q) ≤ f(x) + C`.
  - The single vertex `q = y_{x_0}` already satisfies `f(x) + C − r − s ≤ d(x,q) ≤ f(x) + C − r + s`, by the
    triangle inequality alone.
  - Exactness (`r = 0`) forces all the `y_x` to coincide, i.e. descending paths that merge. Merging paths give HL
    directly, again without Helly.
- **So:** the Helly property of balls never produces the exact realization HL needs. Coarsely it gains at most a factor 2 (a window of width `2r ≥ s` instead of `2s`).

**Why the earlier proofs worked.** They used a Helly theorem for **exact-distance cells**. For an edge `e = uv` and
`k ∈ {−1,0,1}`, put `Q(e,k) = {q : d(u,q) − d(v,q) = k}`. A gradient field `f` chooses one cell per edge. HL on a finite
connected `A` says exactly that the chosen cells on the edges of `A` have a common vertex.
- In median graphs the cells are halfspaces. They are convex, `Q(e,0) = ∅`, the two cells are complementary, and Helly
  number is 2 (`roller-compactifications-of-cube-complexes-are-sfts`).
- In the `{4g,4g}` surface graph the cells are halfplanes, with Helly number 3 in `H²`
  (`horofunction-lemma-holds-for-free-and-surface-groups`).
- Balls are not cells. A ball intersection prescribes only upper bounds on distances.

## 2. In Helly graphs, cells are not a Helly family

Take the king's graph `⊠²L` (`Z²` with the ℓ^∞ metric), which is the paper's basic Helly graph, and the edge
`e = (0,0)(1,0)`.
- `Q(e,0)` contains `(0,5)` and `(0,−5)`.
- Every geodesic between them passes through a vertex `(a,0)`, and `d((0,0),(a,0)) − d((1,0),(a,0)) = |a| − |a−1| = ±1`.
- So `Q(e,0)` is the union of a north cone and a south cone, and it contains no geodesic between them: it is not convex.

A local pattern of radius `≥ 1` does separate the two cones. The HL question for Helly graphs is therefore whether the
refined **R-pattern cells** `Q(v,P) = {q : ∇d(·,q)|_{B_R(v)} = P}` have a finite Helly number with bounded minimal
obstructions. That is the Helly-graph form of the three-move template (halfspace calculus, Helly number, descent). Nothing
in CCGHO addresses it.

## Consequences for the gates

- Hyperbolic Kazhdan groups are Helly (Thm 1.1(1)), but that does not yield HL for them. The general tube lemma
  (bh-g2-buildings) remains the route. Seed uniqueness (`finite-type-branch-blow-ups-are-sft-compactifications`, 4a) is
  already proved.
- Type-preserving uniform `C̃_n` lattices (`n ≥ 2`) are Helly and Kazhdan, and they are not hyperbolic.
  - Their Helly graphs are the natural calibration for HL in a non-hyperbolic Kazhdan case.
  - Seed uniqueness for them needs a cone-type property (TP). The paper's β-stable intervals (Thm 1.2), which it links
    to Cannon's cone types, are the candidate; that link has not been checked.
- Calibration target: HL for the king's graph `⊠²L`. The expected answer is yes. The sublevel sets of locally ℓ^∞-ball-
  like functions are locally convex with axis-parallel sides, so they are quadrants or halfplanes once there are no
  minima. The proof is not written.

## Lesson for general BH

- "Helly" is not one property. The horofunction lemma needs a Helly theorem for the cells that pin EXACT distance
  differences.
- In median and hyperbolic-plane geometries those cells are halfspaces, so Helly for halfspaces does the work.
- Helly graphs have Helly for balls, which only bounds distances from above, a bound the triangle inequality already
  gives. So the Helly-group theorem (every hyperbolic group, `C̃_n` lattices) transfers nothing to HL by itself.
- The live question for Helly groups is whether their R-pattern cells form a Helly-type family. For hyperbolic groups the
  tube lemma answers the same question by other means.
