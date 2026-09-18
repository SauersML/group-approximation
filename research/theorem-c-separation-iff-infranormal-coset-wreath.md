---
rg: 2
id: theorem-c-separation-iff-infranormal-coset-wreath
kind: claim
title: A hyperlinear action with a non-invariant Kazhdan fixed algebra exists iff some infranormal coset wreath over an intermediate subgroup is hyperlinear
distinct_from:
  kt-free-action-hyperlinear-iff-wreath-hyperlinear: that is the equivalence for the single Kun--Thom action over G/Γ; this covers every action whose Γ-fixed algebra is not G-invariant, with arbitrary non-product invariant measures, and reduces all of them to wreaths over subgroups Δ ⊇ Γ
  hyperlinear-wreath-model: that asks for hyperlinearity of the one wreath over G/Γ; this shows the Theorem-C route needs only one wreath over some infranormal non-normal Δ ⊇ Γ, and that nothing else can work
  kt-intermediate-coset-wreaths-are-nonsofic: that proves nonsoficity of W_Δ for the Theorem E pair; this proves hyperlinearity of some W_Δ is forced by, and forces, any Theorem-C action separation
  kun-thom-nonsofic-wreath: that imports Theorems A, C, D, E; this uses Theorem C only, together with the distillation theorem
  kt-hyperlinear-coset-wreath-forces-nonroundable-vertex: that derives HS-instability from a hyperlinear W_K; this shows such a W_K is forced by any hyperlinear action with a non-invariant Kazhdan fixed algebra
---

**ESTABLISHED (proposed; proof in `theorem-c-separation-iff-infranormal-coset-wreath-proof`).**
Let `Γ ≤ G` be countable groups with property (T), `Γ` infranormal in `G`
(Kun--Thom Theorem C hypotheses). For `Δ ≤ G` write
`W_Δ = (⊕_(G/Δ) Z/2) ⋊ G`, let `⟨⟨Γ⟩⟩` be the normal closure, and put

```text
ℱ(Γ,G) = { Δ ≤ G : Γ ≤ Δ and W_Δ is hyperlinear },
Δ_hl(Γ,G) = ∩ ℱ(Γ,G)          (= G if ℱ is empty).
```

Then:

1. **(Hyperlinear floor.)** If `G` is hyperlinear, `Δ_hl ∈ ℱ`, and `Δ_hl` is infranormal
   in `G`: its compression semigroup contains `P_Γ`.
2. **(Equivalence.)** The following are equivalent:
   * (a) some hyperlinear p.m.p. action `G ↷ (X,μ)` has `L^∞(X)^Γ` not `G`-invariant;
   * (b) some `Δ` with `Γ ≤ Δ`, `⟨⟨Γ⟩⟩ ⊄ Δ`, has `W_Δ` hyperlinear;
   * (c) `⟨⟨Γ⟩⟩ ⊄ Δ_hl(Γ,G)`.
   Under (a)–(c) the action `G ↷ ({±1},fair)^(G/Δ_hl)` is hyperlinear and not sofic, and
   `Δ_hl` is infranormal, not normal, and contains `Γ`.
3. **(Free separation.)** If moreover `G` is sofic (e.g. the residually finite Theorem E
   group), then (b) implies `hyperlinear-nonsofic-free-action`: the diagonal action on
   `({±1},fair)^(G/Δ) × ({±1},fair)^G` is free, hyperlinear and not sofic.

## What this kills

The second Attempt of `hyperlinear-nonsofic-free-action` left one escape from the
wreath: a Theorem-C obstruction whose `Γ`-fixed functions generate a non-product
invariant measure on `K^(G/Γ)`. There is no such escape. Any hyperlinear action
with a non-invariant `Γ`-fixed algebra, whatever its measure, already forces a
hyperlinear binary wreath `W_Δ` over the pointwise stabilizer `Δ` of that fixed
algebra (by `hyperlinear-action-distills-to-stabilizer-coset-bernoulli`). So **every
Theorem-C separation is a coset-wreath separation**, and the only freedom left is the
choice of the infranormal non-normal intermediate subgroup `Δ`. Conversely, if every
`W_Δ` with `Γ ≤ Δ`, `⟨⟨Γ⟩⟩ ⊄ Δ` fails to be hyperlinear, then no action of `G`, free
or not, separates hyperlinearity from soficity through Theorem C.

**Corollary (no discount for actions).** For the Theorem E pair, (a) forces a hyperlinear
nonsofic group `W_Δ` (`kt-intermediate-coset-wreaths-are-nonsofic`). So no Theorem-C
proof of `hyperlinear-nonsofic-free-action` for that pair is easier than exhibiting a
hyperlinear nonsofic group.

## Biography of the minimal counterexample (inverter reading)

If the flagship fails for the Theorem E pair through Theorem C, then `Δ_hl ⊇ ⟨⟨Γ⟩⟩`:
every hyperlinear coset wreath over a subgroup containing `Γ` lives over a subgroup
containing the normal closure. Conversely the recipe for a construction is fixed: find
one infranormal non-normal `Δ ⊇ Γ` and a hyperlinear model of `W_Δ`. Larger `Δ` means
fewer lamps and a coarser coset action; `W_Δ` for `[Δ:Γ] < ∞` sits inside `W_Γ`, but
for infinite-index `Δ` there is no inclusion and the problem is genuinely different.

DERIVATION
theorem-c-separation-iff-infranormal-coset-wreath-proof
