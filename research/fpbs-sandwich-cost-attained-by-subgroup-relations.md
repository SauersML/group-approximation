---
rg: 2
id: fpbs-sandwich-cost-attained-by-subgroup-relations
kind: claim
title: In a free action of a finitely generated group, no relation sandwiched over a finite set is cheaper than every finitely generated subgroup containing that set
distinct_from:
  fpbs-relative-sandwich-cost-bernoulli-lower-bound: that compares one action with the Bernoulli shift; this compares, inside one action, arbitrary sandwiches with subgroup sandwiches. It is trivial when F generates Delta, where that one is fixed price, so the two split that node into complementary halves.
  fpbs-free-group-sandwich-cost-is-minimal-overgroup-rank: that is this statement for ambient free groups of finite rank, where it is established with an exact value; this is the general statement for all finitely generated groups.
  fpbs-free-group-sandwich-cost-is-two: that is the F_2 case with non-cyclic K; this is the general subgroup-attainment principle.
  fpbs-pseudocost-localizes-to-fg-sandwich-costs: that expresses pseudocost by sandwich costs of restrictions to finitely generated subgroups; this asks whether each sandwich cost is attained by a subgroup, and so whether pseudocost equals the exhaustion quantity sigma of the passage artifact.
---

**OPEN.** Let `Δ` be a finitely generated group, `F ⊆ Δ` a finite set and
`a` a free p.m.p. action of `Δ`. Put

```text
p^Δ_F(a) = inf { C(E) : E_{a|⟨F⟩} ⊆ E ⊆ E_a },
q^Δ_F(a) = inf { C(E_{a|Δ'}) : Δ' finitely generated, ⟨F⟩ ≤ Δ' ≤ Δ }.
```

Prove that `p^Δ_F(a) ≥ q^Δ_F(a)`.

Each `E_{a|Δ'}` is a sandwich, so `p ≤ q` always, and the claim is
`p = q`. Informally: the cheapest relation between `E_{a|⟨F⟩}` and `E_a` can
be taken to be a subgroup relation. This is a measured, action-level
Hanna Neumann or subgroup-attainment principle.

## Why it matters

- **It is the missing half of RSB beyond fixed price.** Route
  `fpbs-rsb-from-bernoulli-cost-and-subgroup-attainment`
  proves `fpbs-relative-sandwich-cost-bernoulli-lower-bound` from three
  inputs: this claim, `fpbs-free-action-cost-at-least-bernoulli-cost`, and
  Abért–Weiss maximality. The two open inputs are complementary:
  - fixed price is exactly the case `⟨F⟩ = Δ` of RSB, where this claim is
    vacuous;
  - this claim involves no comparison between actions.
- **Place on the flagship.** Via
  `fpbs-fixed-pseudocost-from-relative-sandwich-bound`, RSB gives fixed
  pseudocost, which is the only open input of Route C
  (`fpbs-fixed-price-from-fixed-pseudocost-and-finite-costs`) besides the
  finite-cost node. So Route C now reads:

  ```text
  fpbs-fixed-price-universal ⟸ fixed price for fg groups (the H core, shared with route A)
                                ∧ this claim
                                ∧ fpbs-finite-cost-groups-free-actions-have-finite-cost,
  ```

  plus established imports.
- **Unconditional content.** Let `σ(a)` be the exhaustion quantity
  `sup_F q_F(a)` of Proposition A of the passage artifact
  (`research/artifacts/fpbs/docs/fixed-price-countable-passage.md`). This claim
  implies `PC(a) = σ(a)` for every free p.m.p. action of every countable
  group, with no fixed-price input. The proof takes three steps:
  - localization (`fpbs-pseudocost-localizes-to-fg-sandwich-costs`) gives
    `PC(a) = sup_F inf_Δ p^Δ_F(a|Δ)`;
  - this claim gives `p^Δ_F(a|Δ) ≥ q^Δ_F(a|Δ) ≥ q_F(a)`;
  - Proposition A gives the reverse inequality `PC ≤ σ`.

  This is not a graph node; it is stated here as motivation. Contrapositive: a
  strict inequality `PC(a) < σ(a)` for some free action would produce a
  sandwich over a finite set that is cheaper than every subgroup relation.

## Known cases

- **`F` generates `Δ`.** This is trivial: take `Δ' = Δ`.
- **`Δ` free of finite rank.** This is established:
  `fpbs-free-group-sandwich-cost-is-minimal-overgroup-rank` gives
  `p = q = min{rk L : ⟨F⟩ ≤ L}` for every free action.
- **`Δ` amenable.** Here `p` is attained at `E_{a|⟨F⟩}` (RSB node, known
  cases).
- **`⟨F⟩` infinite, and some finitely generated `Δ' ⊇ F` with `C(a|Δ') = 1`.**
  Then `q ≤ 1 ≤ p`. Every sandwich has infinite classes, because `a` is free
  and `⟨F⟩` is infinite, and a relation with infinite classes costs at least
  1 (Levitt). This covers, for example:
  - every `F` in `F_n × Z`, with `Δ' = ⟨F, z⟩` for the central generator `z`;
  - every `F` in a group with an infinite, finitely generated, normal,
    amenable subgroup `N`, with `Δ' = ⟨F, N⟩`.

  It uses standard facts, cited here without a graph node: Levitt's bound, and
  cost 1 for groups with an infinite normal amenable subgroup.

## First open test

Let `Δ = π_1(Σ_g)` with `g ≥ 2`, and let `F` generate a free subgroup of
rank 2 and infinite index. Finitely generated overgroups of `⟨F⟩` are free of
rank at least 2, or of finite index with cost at least `2g − 1`. So `q = 2`,
and the claim says every sandwich costs at least 2. The free-group proof needs
two things:
- an `L²` lower bound for sandwiches, the Fox rank of
  `fpbs-sandwich-cost-fox-rank-lower-bound`;
- an exact identification of that rank with the least overgroup rank,
  Jaikin-Zapirain's `L²`-subgroup rigidity.

For surface groups the second is Jaikin-Zapirain's conjecture that locally
indicable groups are `L²`-subgroup rigid. The first needs a relative Fox
calculus for a one-relator group.

## Attempts

**Construct the subgroup from the sandwich (September 19, 2026, w18c-fp-alt, group-rings).**

The direct attack does not work. Take a sandwich `E` and a graphing of it: the
generators of `⟨F⟩` together with partial maps `φ_i`. Each `φ_i` is a
countable union of pieces `γ|_B` with `γ ∈ Δ`. Then take `Δ'` generated by
`F` and the `γ` that were used.

It dies on measure. The piece `γ|_B` costs `μ(B)`, but `E_{a|Δ'}` contains
the whole graph of `γ`, which costs up to 1. For example, take
`E = E_{a|⟨F⟩} ∨ graph(γ|_B)` with `μ(B) = ε`. Then
`C(E) ≤ C(E_{a|⟨F⟩}) + ε`, while nothing bounds `C(a|⟨F, γ⟩)` by that
quantity.

The free-group proof avoids any construction. It squeezes `p` between an
`L²` invariant, the Fox rank, and a subgroup treeing, and the two agree by
`L²`-subgroup rigidity. The attack should follow the same pattern. For a
general `Δ` this needs two ingredients:
- a lower bound `C(E) ≥ ρ_F` for every sandwich, where `ρ_F` is a relative
  `L²` invariant of `⟨F⟩ ≤ Δ`;
- a finitely generated `Δ' ⊇ F` with `C(a|Δ') = ρ_F`.

The second fails as stated whenever `Δ'` does not have fixed price with cost
equal to its `L²` bound. So beyond locally indicable, `L²`-rigid ambient
groups, the natural route runs into the cost-versus-`β_1^{(2)}` problem. This
is deferred to the surface test above.
