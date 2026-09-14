---
rg: 2
id: lot-at-most-seven-vertices-census-proof
kind: route
title: Enumerate all reduced trees with seven vertices and certify each by a primary-source asphericity test on the presentation, on a Tietze presentation, or relative to sub-trees
target: lot-complexes-with-at-most-seven-vertices-are-aspherical
requires:
  - lot-complexes-with-at-most-six-vertices-are-aspherical
artifacts:
  - research/artifacts/hl-whitehead-lot-certify-2026-09-14.md
---

Notation as in the claim.

## 1. Reduction

By the reduction step of `lot-at-most-six-vertices-census-proof`, a LOT with at most seven
vertices is homotopy equivalent to a reduced LOT with at most seven vertices. Those with at most
six are covered by `lot-complexes-with-at-most-six-vertices-are-aspherical`, so only reduced LOTs
with exactly seven vertices remain. They are enumerated as in that route, over all 11 tree shapes.

## 2. Tests

Every test below implies asphericity of K(Γ).

**(inj), (IT).** As in the six-vertex route.

**(itest).** Barmak--Minian, arXiv:1601.00604:
- "Theorem 2.6. If P satisfies the I-test, it is aspherical."
- For a LOT, the vector v must be orthogonal to e_{i(e)} − e_{t(e)} for every edge, so
  v = ±(1, ..., 1).
- The orderings of Definition 2.5 are found greedily, which is complete by Remark 2.9, and then
  re-verified.

**(weight).** Harlander--Rosebrock, arXiv:1912.12512v2:
- Definition 3.5 is the weight test "which implies the asphericity of L": (1) the corner weights
  of a 2-cell with q corners sum to at most q − 2, and (2) every reduced cycle in lk(L) has weight
  at least 2.
- The census uses nonnegative rational weights, verified exactly. Every reduced cycle then
  contains a simple cycle of weight at least 2.
- The minimum simple cycle is computed exactly, as min over edges e = uv of w(e) + dist_{G−e}(u, v).

**(Tietze).**
- *Move.* If a generator x occurs exactly once in a relator r, then eliminating x is a Tietze
  transformation: substitute its solution into the other relators, then delete x and r.
- *Homotopy type.* The move is realised by Andrews--Curtis moves (multiplying the other relators
  by conjugates of r^{±1}) followed by collapsing the 1-cell x across the 2-cell r. So it is a
  3-deformation and preserves homotopy type, deficiency 1, H₁ = Z and exponent sums 0.
- *Label presentations.* These eliminate exactly the vertices that label no edge.
- *Theorems applied.* Barreto--Minian, arXiv:2308.07447v1, Theorem 2.5, on minima, or on maxima
  (Remark 2.3) after inverting every generator. Also their Theorem 2.18. Both give local
  indicability, and H₂ = 0 then gives asphericity.

**(relative).** Harlander--Rosebrock, arXiv:1912.12512v2:
- *Theorem 3.4.* Let K = K_1 ∨ ... ∨ K_n ⊆ L, where the 2-cells of L have exponent sum 0 and the
  K_i are full. If lk+(L) or lk−(L) is a forest relative to lk±(K), then L is VA relative to K.
- *Theorem 2.4.* "if K is aspherical, then so is L".
- *Choice of K.* The K_i are the complexes of vertex-disjoint sub-LOTs.
  - Fullness is checked: every edge whose three letters lie in the union is in K.
  - lk+ and lk− are the graphs I(Γ) and T(Γ), and each sub-LOT's vertex set is collapsed.
  - Each sub-LOT complex is certified recursively by these tests. A wedge of aspherical
    2-complexes is aspherical.

## 3. Census and results

**Runs.** `experiments/lot-asphericity-census/census_primary.py` and `lot_primary.py` (MSI job
781699) produce `outp57/n7_s*_tally.json`. Over the 279943 classes, the first passing test is:

| test | classes |
|---|---|
| inj | 48142 |
| IT | 231212 |
| itest | 51 |
| weight | 159 |
| L-bm25 | 354 |
| relative | 12 |
| none | 13 |

**Tietze closure.** `survivorsp4.py` and `lot4.py` (MSI job 784526) run a breadth-first closure
under eliminations from the LOT presentation. All 13 remaining classes reach a presentation
satisfying Theorem 2.5. The eliminated generators and relators are in
`outp57/survivorsp4_n7.jsonl`.

**Calibration.** As in the artifact, §2. For the relative and Tietze steps, see the artifact, §3.

So every reduced LOT with seven vertices passes a test, which proves the claim.
