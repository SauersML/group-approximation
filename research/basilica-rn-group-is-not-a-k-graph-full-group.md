---
rg: 2
id: basilica-rn-group-is-not-a-k-graph-full-group
kind: claim
title: If a self-similar group H has a nonzero character psi with psi(h) = sum_x psi(h|_x), then V_d(H) is the full group of no aperiodic finite k-graph, for any k >= 1; so the basilica and odometer Roever-Nekrashevych groups have no k-graph model
distinct_from:
  torsion-germ-rn-groups-are-not-k-graph-full-groups: that excludes k-graph models through torsion or non-Hausdorff fixed-point germs, and leaves the basilica open; this uses rational groupoid homology, applies to torsion-free H with Hausdorff germ groupoid, and settles the basilica for every k, including k = 1.
  rn-lamplighter-is-f-infinity-and-acyclic-via-a-2-graph: that realises V_2 of the lamplighter as a 2-graph full group; this gives a necessary condition, rational acyclicity of the germ groupoid, that the lamplighter meets and the basilica fails.
  li-finite-k-graph-full-groups-are-f-infinity: that is Li's finiteness theorem for k-graph full groups; this shows it cannot be applied to V_2(basilica) or V_2(odometer), for any k.
  contracting-rover-nekrashevych-groups-are-f-infinity: that asks whether V_d(G) is F_infinity for contracting G; this rules out k-graph models for a named class and proves no finiteness.
  finite-k-graph-boundary-groupoid-standard-facts: that records the standard facts about k-graph groupoids; this adds that every arrow lies in a full bisection and that H_0 = 0 rationally forces all rational homology to vanish.
artifacts:
  - experiments/rn-lamplighter-finiteness-2026-09-17/section_characters.py
  - experiments/rn-lamplighter-finiteness-2026-09-17/results-section-characters.txt
---

**ESTABLISHED (proof in `basilica-rn-group-is-not-a-k-graph-full-group-proof`; lane proof, w12-101; not
independently reviewed).** The imported inputs are Rubin's theorem and Lemmas B and C of
`torsion-germ-rn-groups-are-not-k-graph-full-groups-proof`, and the Koszul-complex computation of `k`-graph
groupoid homology (Farsi–Kumjian–Pask–Sims, arXiv:1808.07807). Everything else is proved in full. In particular,
neither Li's theorems nor Matui's AH conjecture is used.

## Setting

- `H ≤ Aut(X^*)` is a faithful self-similar group on `X = {0, ..., d-1}`, with `d ≥ 2`.
- `V_d(H)` is its Röver–Nekrashevych group, and `𝒢_H = Germ(V_d(H) ↷ X^ω)` is its germ groupoid.
- `Λ` is a finite `k`-graph (any `k ≥ 1`) with hypothesis **(H)** of `torsion-germ-rn-groups-are-not-k-graph-full-groups`:
  it is aperiodic, and every vertex receives and emits at least two edges of each colour.
- `G_Λ` is its path groupoid, and `F(G_Λ)` its topological full group.
- A **section character** of `H` is a homomorphism `ψ : H → Q` with `ψ(h) = Σ_{x ∈ X} ψ(h|_x)` for all `h ∈ H`.

## Statement

1. **Rigidity.** If `V_d(H) ≅ F(G_Λ)` as abstract groups, then `𝒢_H ≅ G_Λ` as topological groupoids. In
   particular every arrow of `G_Λ` lies in a full bisection, and `H_*(𝒢_H) ≅ H_*(G_Λ)`.
2. **Rational acyclicity is necessary.** If `V_d(H) ≅ F(G_Λ)`, then `H_n(𝒢_H; Q) = 0` for every `n`.
   - The reason: `H_0(𝒢_H)` is a quotient of `Z/(d-1)`, so it vanishes rationally. For a finite `k`-graph, rational
     vanishing of `H_0` forces rational vanishing of all of `H_*(G_Λ)`. The proof decomposes the Koszul complex
     into joint generalised eigenspaces of the commuting adjacency matrices.
3. **Section-character obstruction.** A section character `ψ` gives a homomorphism `H_1(𝒢_H; Z) → Q` that sends the
   class of the full bisection of `h ∈ H` to `ψ(h)`. So if `H` has a nonzero section character, then
   `H_1(𝒢_H; Q) ≠ 0`, and `V_d(H)` is **not** the full group of any finite `k`-graph with (H), for any `k ≥ 1`.
4. **Basilica.** `IMG(z² - 1)`, with `a = σ(1, b)` and `b = (1, a)`, has the section character `ψ = ` exponent sum,
   `ψ(a) = ψ(b) = 1`. The proof that it is well defined on the group is a direct contraction argument, given in the
   proof file.
   - **Answer to the question left open by `torsion-germ-rn-groups-are-not-k-graph-full-groups`:**
     `V_2(Basilica)` is not a `k`-graph full group for any `k ≥ 1`. This includes `k = 1`, the Cuntz–Krieger or graph
     full groups.
   - The same holds for the **odometer** `a = σ(1, a)`, with `ψ(a) = 1`.
5. **Calibration.** Section characters are computed in `section_characters.py`:
   - the lamplighter `a = σ(a, b)`, `b = (a, b)` has none, as it must, since it is a 2-graph full group;
   - Grigorchuk, Hanoi and Thompson's `V` (trivial `H`) have none;
   - basilica and odometer have a one-dimensional space of them.
   The script also checks that every trivial reduced basilica word of length `≤ 8` (16 of them) has exponent sum 0.

## What this settles and what it leaves

- **The `k`-graph route to `F_∞` is closed for the basilica for every `k`**, not only `k ≥ 2`, and without the
  hyperbolicity input of w11's remark. `V_2(Basilica)` is `F_∞` anyway, by the bounded-automata theorem cited in
  `torsion-germ-rn-groups-are-not-k-graph-full-groups`.
- Via (Ab) of `rover-nekrashevych-finite-presentation-criteria`, a section character is the same as a nonzero map
  `V_d(H)^ab → Q` for even `d`. So for even `d` and finitely generated `H`, **a Röver–Nekrashevych group with infinite
  abelianisation is never a finite `k`-graph full group.** For odd `d` the same holds, since (Ab) only adds a `Z/2`.
- Part 2 is stronger than part 3. It asks for the whole rational homology of `𝒢_H` to vanish. It is the test to run
  on the `S`-arithmetic affine candidates, the next target of this lane.
