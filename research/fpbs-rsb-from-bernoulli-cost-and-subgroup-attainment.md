---
rg: 2
id: fpbs-rsb-from-bernoulli-cost-and-subgroup-attainment
kind: route
title: Pass the Bernoulli sandwich through a subgroup relation, compare subgroup costs by fixed price in finitely generated groups, and return to the action through subgroup attainment
target: fpbs-relative-sandwich-cost-bernoulli-lower-bound
requires:
  - fpbs-free-action-cost-at-least-bernoulli-cost
  - fpbs-bernoulli-maximal-cost
  - fpbs-sandwich-cost-attained-by-subgroup-relations
  - gaboriau-treeable-free-action-realizes-min-cost
---

Let `Δ` be finitely generated, `F ⊆ Δ` finite, and `a` a free p.m.p. action
of `Δ`. Let `s = s_Δ` be the Bernoulli shift on `[0,1]^Δ`. Let `𝒮` be the set
of finitely generated `Δ'` with `⟨F⟩ ≤ Δ' ≤ Δ`. It contains `Δ`, so it is
not empty.

**Step 0. `s` is free.** Take `g ≠ 1`. If `g x = x`, then `x` is constant on
every coset `h⟨g⟩`. So two distinct coordinates of `x` agree, which is a
null event for i.i.d. Lebesgue coordinates. There are countably many `g`, so
`s` is essentially free. Hence for every `Δ' ≤ Δ`, both `s|Δ'` and `a|Δ'` are
free p.m.p. actions of `Δ'`.

**Step 1. `C(E_{s|Δ'}) ≤ C(E_{a|Δ'})` for every `Δ' ∈ 𝒮`.**

*Case `Δ'` infinite.* `Δ'` is infinite and finitely generated. By
`fpbs-bernoulli-maximal-cost`, some nontrivial Bernoulli action `b` of `Δ'`
attains the supremum of costs of free p.m.p. actions of `Δ'`. So
`C(s|Δ') ≤ C(b)`. By `fpbs-free-action-cost-at-least-bernoulli-cost`,
applied to the free action `a|Δ'` and the nontrivial Bernoulli shift `b`,
`C(b) ≤ C(a|Δ')`.

*Case `Δ'` finite, of order `n`.* Let `c` be any free p.m.p. action of `Δ'`
on a standard probability space `(Y, ν)`.
- Fix a Borel linear order of `Y`, and let `T` be the set of points that are
  least in their orbit. It is Borel, it meets every orbit exactly once, and
  its `n` translates partition `Y`. So `ν(T) = 1/n`.
- The graphing `{c(g)|_T : g ∈ Δ' ∖ {1}}` joins each orbit as a star with
  `n − 1` edges, so it is a treeing of `E_c`. Its cost is `(n − 1)/n`.
- By `gaboriau-treeable-free-action-realizes-min-cost` (1),
  `C(E_c) = 1 − 1/n`.

Apply this to `c = s|Δ'` and to `c = a|Δ'`. The two costs are equal.

**Step 2. Chain.** For every `Δ' ∈ 𝒮`, `E_{s|⟨F⟩} ⊆ E_{s|Δ'} ⊆ E_s`. So
`E_{s|Δ'}` is a sandwich for `s`, and

```text
p^Δ_F(s) ≤ inf_{Δ' ∈ 𝒮} C(E_{s|Δ'})
         ≤ inf_{Δ' ∈ 𝒮} C(E_{a|Δ'})      (Step 1)
         =  q^Δ_F(a)
         ≤ p^Δ_F(a)                        (fpbs-sandwich-cost-attained-by-subgroup-relations).
```

This is the target. ∎

## Remarks

**What is used where.**
- `fpbs-free-action-cost-at-least-bernoulli-cost` is used only for the
  groups `Δ' ∈ 𝒮`. These are finitely generated subgroups of `Δ` containing
  `F`, not `Δ` itself.
- The subgroup-attainment input is used only for the action `a`, never for
  the Bernoulli shift.
- For `⟨F⟩ = Δ`, the input is vacuous and the route is the fixed-price case.

**Split of RSB.**

```text
RSB  ⟸  (fixed price for fg groups)  ∧  (subgroup attainment),
```

The two conjuncts are logically complementary. The first is RSB at
`⟨F⟩ = Δ`. The second is empty there and makes no comparison between
actions. Route C (`fpbs-fixed-price-from-fixed-pseudocost-and-finite-costs`,
through `fpbs-fixed-pseudocost-from-relative-sandwich-bound`) therefore needs
exactly one input beyond route A's finitely generated core and the finite-cost
node: `fpbs-sandwich-cost-attained-by-subgroup-relations`.

**Unconditional slice.** For `Δ` free of finite rank, subgroup attainment and
fixed price are both known, and the conclusion holds with an exact value
(`fpbs-free-group-sandwich-cost-is-minimal-overgroup-rank`).
