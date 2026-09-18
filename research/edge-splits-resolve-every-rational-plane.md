---
rg: 2
id: edge-splits-resolve-every-rational-plane
kind: claim
title: Repeated edge-midpoint splits of a unimodular triangle cone make any rational plane a union of piece edges, so edge-split dissections are cofinal among all rational polyhedral dissections
distinct_from:
  edge-split-operad-satisfies-ore: that asks for common refinements inside the edge-split operad, ordered by operad refinement; this is the geometric input, that edge-split dissections refine every rational polyhedral dissection, and it says nothing about the operad order.
  unimodular-dissections-have-egyptian-fraction-volumes: that bounds the number of dissections with a given piece count; this is an exact Euclid-type resolution statement for planes.
  transvections-are-single-carets-of-the-edge-split-operad: that shows the linear group acts by single edge-split carets; this shows edge splits alone reach every rational polyhedral shape.
---

**ESTABLISHED** for `m = 2` (lane bh-free-54, 2026-09-18). Lane proof below;
elementary, not independently reviewed. Open for `m ≥ 3`, with evidence.

## Statement (`m = 2`)

- **Setting.** Let `P = cone(w_0, w_1, w_2)` be a unimodular cone in `R^3`, with
  its frame a `Z`-basis. `𝒪_E(P)` is the set of dissections obtained from `P` by
  repeatedly splitting one piece `cone(p, q, r)` at an edge midpoint:
  `cone(p, p+q, r) ⊔ cone(p+q, q, r)`.
- **Part 1.** For every rational plane `Π` there is a `D ∈ 𝒪_E(P)` none of whose
  pieces has interior meeting `Π`.
- **Part 2 (cofinality).** For every finite set of rational planes, and so for every
  rational polyhedral dissection of `P` (in particular every unimodular dissection),
  some `D ∈ 𝒪_E(P)` refines it.

This is the two-dimensional (projective) analogue of "every rational point is a
Stern–Brocot vertex": every rational line in the triangle becomes a union of edges.

## Proof of Part 1

- **Values.** Write `Π = ker ℓ` with `ℓ` integral, and `λ_k = ℓ(w_k)`. Splitting
  at the edge `(w_a, w_b)` gives two children. One has `λ_b` replaced by
  `λ_a + λ_b`; the other has `λ_a` replaced by `λ_a + λ_b`.
- **Crossing.** A piece is *crossed* if its values have both strict signs. A crossed
  edge is a pair `(a, b)` with `λ_a λ_b < 0`, and its *complexity* is
  `|λ_a| + |λ_b|`. Let `Φ` be the sum of the complexities of the crossed edges.
  `Φ` is a positive integer on crossed pieces.
- **One crossed edge.** The values are `(0, t, s)` with `t > 0 > s`. Split the
  crossed edge.
  - If `t + s = 0`, neither child is crossed.
  - If `t + s > 0`, only the child `(0, t + s, s)` is crossed, and its
    `Φ = t < t + |s|`.
  - The case `t + s < 0` is symmetric.
- **Two crossed edges.** There is an odd vertex `v` with value `s`. The other two
  vertices have values `t_1, t_2` of the opposite sign, and we may take
  `|t_1| ≥ |t_2|`. Then `Φ = 2|s| + |t_1| + |t_2|`. Split the edge `(v, w_1)` at
  `u = v + w_1`, whose value is `s + t_1`.
  - **If `|t_1| ≥ |s|`.**
    - The child `(u, w_1, w_2)` has one sign, so it is not crossed.
    - The child `(v, u, w_2)` has `Φ ≤ |t_1| + |s| + |t_2|`, which is smaller by at
      least `|s|`.
  - **If `|t_1| < |s|`.**
    - The child `(v, u, w_2)` has odd vertex `w_2` and
      `Φ = 2|t_2| + 2|s| − |t_1|`. This is smaller by `2|t_1| − |t_2| ≥ |t_1|`.
    - The child `(u, w_1, w_2)` has odd vertex `u` and `Φ = 2|s| − |t_1| + |t_2|`.
      This is smaller by `2|t_1|`.
- **Termination.** Every crossed child has strictly smaller `Φ`. So every branch
  stops, and the binary tree of splits is finite.

## Proof of Part 2

- Resolve the planes one at a time, applying Part 1 inside each current piece in that
  piece's own frame. Edge-split dissections compose, so the result is in `𝒪_E(P)`.
- Each final piece lies in one cell of the arrangement of all the planes spanned by
  the faces of the given dissection. Hence it lies in one of that dissection's
  pieces.

## Higher rank (open)

- **The rule.** In rank `r = m + 1`, split the crossed edge with the largest
  `|λ_a| + |λ_b|`.
- **Evidence.** This greedy rule resolved every one of 825 random primitive forms
  in ranks 4, 5 and 6 (entries at most 12), at depth at most 48 (MSI; script `ldgen.py`
  in `research/artifacts/gq-bh-free-54-edge-split-ore-tests.md`).
- **The gap.** No potential function is proved for `m ≥ 3`. In the Egyptian-fraction
  node's language, the needed statement is that edge splits make every rational
  hyperplane a union of faces. `Mod(S_g)` needs rank `6g − 6`.

## Lesson for general BH

- **Two confluence questions, one settled.** Edge splits are a Euclid algorithm for
  planes. The geometric half of confluence (cofinality) is elementary and
  quantitative, via the complexity potential. So for the edge-split operad, the
  whole finite-presentation difficulty sits in the operad order: whether geometric
  refinement implies refinement by splits (`edge-split-operad-has-common-refinements`),
  not whether refinements exist.
- **Worth doing for any operad host.** For any dissection-operad host of BH, prove
  cofinality by a potential first. It isolates the genuinely non-LCM part of the
  problem.
