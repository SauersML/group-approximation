---
rg: 2
id: periodic-k-graph-subgroups-with-ray-cocycle-are-finite
kind: claim
title: In the topological full group of a finite aperiodic k-graph, a finitely generated periodic subgroup whose degree cocycle stays on one ray Zv (v in N^k) is finite; so in nV and in Kohl's CT(Z) infinite periodic subgroups, if any, need two independent stacks
distinct_from:
  brin-thompson-2v-is-torsion-locally-finite: that is the open statement for all of 2V; this proves it for every subgroup whose level cocycle lies on a ray, the regime where two stacks move in lockstep.
  almost-automorphism-torsion-subgroups-are-rf: that is the one-dimensional pumping (1-graphs, with tree sections); this is the same pumping run along a ray of a higher-rank degree lattice, without sections.
  brin-thompson-torsion-has-clopen-fixed-sets: that gives the coboundary criterion for finiteness in nV; this produces the coboundary (in fact a finite permutation model) whenever the cocycle is confined to a ray.
artifacts:
  - research/artifacts/gq-bh-bh-kourovka-problems.md
---

**ESTABLISHED** (lane proof, elementary, not reviewed). No imported theorems. No
priority is claimed. It is the one-stack pumping of bh-free-12 and bh-free-06, run along
a ray of `Z^k`.

## Setting

Let `Λ` be a finite, row-finite `k`-graph with no sources, with `|vΛ^{e_i}| ≥ 2` for every
vertex `v` and every `i`, and aperiodic, so that its boundary groupoid is effective.
- **Paths and cylinders.** On `Λ^∞`, the cylinders are `Z(λ) = λΛ^∞`. For
  `d(λ) ≤ d(τ)`, `Z(λ) ∩ Z(τ) ≠ ∅` iff `τ(0, d(λ)) = λ`, and then `Z(τ) ⊆ Z(λ)`.
- **The full group.** `F(Λ)` is the group of homeomorphisms `h` given by two partitions
  `{Z(λ_i)}`, `{Z(μ_i)}` and pieces `h(λ_i w) = μ_i w`, with `s(λ_i) = s(μ_i)`. This is
  the topological full group of the boundary groupoid.
- **Degree cocycle.** `c(h, x) = d(μ_i) − d(λ_i) ∈ Z^k` for `x ∈ Z(λ_i)`.
  - It is well defined: refinement preserves it, and two pieces at `x` with different
    degree changes would give a nontrivial isotropy bisection acting trivially on an open
    set, contradicting effectiveness.
  - It is locally constant, and satisfies `c(gh, x) = c(g, hx) + c(h, x)`.

## Theorem

Let `H ≤ F(Λ)` be finitely generated and periodic, and suppose `c(h, x) ∈ Zv` for all
`h ∈ H` and `x`, for some `v ∈ N^k ∖ {0}`. Then `H` is finite. More precisely, `H` embeds
in the symmetric group of a finite set of cylinders.

It suffices that the generators satisfy the ray condition, since the cocycle identity
propagates it.

## Proof

Write `c(h, x) = κ(h, x) v`. Fix a symmetric generating set `S` of `H`, and choose:
- `D` with every piece of every `s ∈ S` of source and target degree `≤ D·1`;
- `K = max |κ(s, ·)|`;
- `E = (D + K‖v‖_∞)·1`, `C = |Λ^E|` (finite), and `B = K·C`.

1. **Contraction.** If `h` maps a cylinder `Z(τ)` onto `Z(τν)` with `d(ν) ≠ 0`, then `h`
   has infinite order.
   - `h^j Z(τ) ⊆ Z(τν)` for all `j ≥ 1`.
   - `Z(τν) ⊊ Z(τ)`, because `|s(τ)Λ^{d(ν)}| ≥ 2`.
2. **Pumping: `|κ(h, x)| ≤ B` on `H`.**
   - Suppose `h = s_m ⋯ s_1` with `x_i = s_i x_{i−1}` and heights
     `ht(i) = Σ_{j≤i} κ(s_j, x_{j−1})`, and `ht(m) > B`. (For negative heights, pass to
     `h^{-1}` at `hx`.)
   - The record times `t_ℓ = max{i : ht(i) ≤ ℓ}` take more than `C` distinct values. So
     two of them, `t < t'`, have `x_t` and `x_{t'}` in one cylinder `Z(τ)` with
     `d(τ) = E`, and `r = ht(t') − ht(t) > 0`.
   - Since `t` is a record time, `ht(i) ≥ ht(t)` on `[t, t']`. By induction, and because
     `v ≥ 0`, `s_i ⋯ s_{t+1}` maps `Z(τ)` onto a single cylinder `Z(τ_i)` by `τw ↦ τ_i w`,
     with `d(τ_i) = E + (ht(i) − ht(t))v ≥ D·1`.
   - The step uses the cylinder fact: `Z(τ_i)` lies inside one piece `Z(λ)` of
     `s_{i+1}`, and `s_{i+1}(λρw) = μρw`.
   - At `i = t'`, `Z(τ_{t'}) ∋ x_{t'} ∈ Z(τ)` and `d(τ_{t'}) = E + rv ≥ E`. So
     `Z(τ_{t'}) = Z(τν) ⊊ Z(τ)`.
   - By step 1, `s_{t'} ⋯ s_{t+1}` has infinite order. This contradicts periodicity.
3. **Deep cylinders move as single pieces.** Put `L = D + B‖v‖_∞`. By induction on word
   length and step 2, every `h ∈ H` maps every `Z(τ)` with `d(τ) ≥ L·1` onto a cylinder
   `Z(τ')` by `τw ↦ τ'w`, with `d(τ') − d(τ) = κv` and `|κ| ≤ B`.
4. **Finite permutation model.** Fix `n ≥ L + B‖v‖_∞`. The set
   `F_n = {h Z(τ) : h ∈ H, d(τ) = n·1}` consists of cylinders of degrees
   `n·1 + κv`, `|κ| ≤ B`, so it is finite. By step 3, `H` permutes it.
   - If `h` fixes every member, it maps each degree-`n·1` cylinder `Z(τ)` onto itself by
     `τw ↦ τ'w`.
   - `κ ≠ 0` would make `Z(τ')` a proper sub- or super-cylinder, so `κ = 0` and
     `τ' = τ`. Hence `h = 1`, and `H ↪ Sym(F_n)`. ∎

## Consequences

- **Brin–Thompson `nV`.** Take `Λ` to be the product of `n` one-vertex graphs with two
  loops.
  - Every finitely generated periodic subgroup of `nV` whose level cocycle takes values
    in `Zv`, `v ∈ N^n ∖ {0}`, is finite. Examples are `V` acting in one coordinate, or
    diagonally.
  - This includes Röver's theorem for `V`. It is the regime of
    `brin-thompson-2v-is-torsion-locally-finite` in which the two stacks move in
    lockstep.
- **Kohl's `CT(Z)` (Kourovka 19.46, 17.58).** A finitely generated subgroup of `CT(Z)`
  lies in some `CT_P(Z)`, `P` finite. `CT_P(Z)` is `F(Λ_P)` for the carry-rule one-vertex
  `k`-graph (`ct-p-z-is-a-one-vertex-k-graph-full-group`), which is aperiodic with
  `p ≥ 2` edges of colour `p`. Its degree cocycle is `(v_p(slope))_p`.
  - Hence every finitely generated periodic subgroup of `CT(Z)` whose slopes all lie in
    `γ^Z`, for an integer `γ ≥ 2`, is finite.
  - An infinite finitely generated periodic subgroup of `CT(Z)`, which would answer
    19.46, must have slope group not contained in any `γ^Z`. So it has rank `≥ 2`, or it
    is generated by a non-integral ratio such as `3/2`.
  - Any torsion group of intermediate growth, such as a Grigorchuk group, inside
    `CT(Z)` (which would answer 17.58) is subject to the same constraint.
- **Open boundary.** The proof needs `v ≥ 0`: along a mixed-sign direction such as
  `(−1, 1)` (slope `3/2`) the image cylinders are not nested, and step 2 breaks. That is
  exactly the Collatz-type `3/2` regime, and it is left open, as is rank `≥ 2`.

## Lesson for general BH

Torsion local finiteness in Thompson-type hosts is a statement about the **rank and
cone position of the degree cocycle**, not about the host.
- **The one-stack mechanism.** Pumping plus contraction works for any `k`-graph full
  group as long as the cocycle is confined to one ray of the positive cone. So every
  higher-rank host contains a large torsion-locally-finite regime.
- **Where the Burnside hosts must live.** Infinite finitely generated periodic groups,
  and hence Burnside-type BH inputs such as BBMZ 5.3(6), can only live in the part of a
  higher-rank host where the cocycle is at least 2-dimensional, or is 1-dimensional but
  mixed-sign.
- **Where Belk–Bleak undecidability lives.** That same part is where the torsion
  problem becomes undecidable (Belk–Bleak, arXiv:1405.0982, for `2V`, as recorded in
  `research/artifacts/gq-bh-bh-free-06-one-stack-pumping.md`; not read at source here). Constructions of periodic subgroups should target it
  directly.
- **Parallel with the Out results.** This is the same one-base/two-base split as the
  Cobham rigidity behind `out-ct-p-z-is-c2`: one base is tame, two independent bases
  carry the complexity.
