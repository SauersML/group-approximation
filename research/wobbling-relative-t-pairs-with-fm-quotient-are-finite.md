---
rg: 2
id: wobbling-relative-t-pairs-with-fm-quotient-are-finite
kind: claim
title: "If (Γ, H) has relative property (T) with H normal and Γ/H has Cornulier's Property FM, then every homomorphism from Γ to the wobbling group of Z, or to the full-shift topological full group, has finite image"
distinct_from:
  full-shift-full-group-kazhdan-subgroups-are-finite: that is the case where Γ itself has (T); this needs (T) only relative to a normal subgroup plus Property FM of the quotient, which also holds for FM groups without (T) and without FA, such as Cornulier's S-arithmetic lattices G(Z[1/p])
  wobbling-normal-relative-t-subgroups-are-locally-finite: that proves H is locally finite for every Γ; this proves the whole image of Γ is finite once Γ/H has FM, so a witness needs a quotient without FM
  full-shift-full-group-has-infinite-normal-relative-t-subgroup: that asks for a witness pair; this excludes every witness whose quotient has FM
  elementary-linear-semidir-pair-relative-t: that supplies relative-(T) pairs; this shows the ones whose quotient has FM have no infinite image in W(Z)
---

**ESTABLISHED** by `wobbling-relative-t-fm-quotient-finite-proof`.
- Imported verbatim from Y. Cornulier, *Irreducible lattices, invariant means, and commensurating
  actions*, arXiv:1308.1318v3: Definition 1.2, Example 2.7, Proposition 5.6, Theorem 6.12,
  Theorem 7.1(2). The quotations are in the proof route.
- Also used: the faithful action of `[[X]]` on a dense `σ`-orbit by bounded-displacement
  permutations, the same identification as in `wobbling-normal-relative-t-subgroups-are-locally-finite`.
- Lane proof by swarm-0917-w21-w21-nv-last1. Not independently reviewed. No priority claimed: this is
  a direct combination of Cornulier's theorems.

## Setting

- `W(Z)` is the group of bijections `f : Z → Z` with `sup_n |f(n) − n| < ∞`.
- `X = {0,1}^Z` and `[[X]]` is its topological full group.
- **Property FM** (Cornulier, Def. 1.2, verbatim): "A locally compact group G has Property FM if
  for every continuous discrete G-set X with a G-invariant mean on all subsets of X, there exists a
  finite G-orbit." For a discrete group this is the negation of Glasner–Monod's class (B).
- **Relative (T)** for `H ⊴ Γ`: every unitary representation of `Γ` with almost invariant vectors
  has a nonzero `H`-invariant vector.

## Statement

Let `Γ` be a discrete group and `H ⊴ Γ` with `(Γ, H)` relative (T) and `Γ/H` with Property FM.

1. `Γ` has Property FM, and `Γ` is finitely generated.
2. Every homomorphism `ρ : Γ → W(Z)` has finite image. More generally this holds for `Wob(Y)`,
   for any discrete metric space `Y` of uniformly subexponential growth.
3. Every homomorphism `ρ : Γ → [[X]]` has finite image.
4. **(Class kill.)** If `Γ ≤ [[X]]` (or `Γ ≤ W(Z)`) and `H ⊴ Γ` is infinite with `(Γ, H)` relative
   (T), then `Γ/H` is non-amenable and does not have Property FM.

## What it kills

In `full-shift-full-group-has-infinite-normal-relative-t-subgroup`, the invariant is **Property
FM of the quotient `Γ/H`**. Every member of the class dies at one step: Theorem 6.12 transfers FM
from `Γ/H` up to `Γ` along the Kazhdan quotient map, and then Theorem 7.1(2) makes the image in
`W(Z)` finite. The class contains:
- every quotient with (T), for example `EL_n(R) ⋉ R^n` with `n ≥ 3` and `R` finitely generated;
- every quotient that is an irreducible lattice in a product with a (T) factor (Cornulier Thm 1.13),
  including ones without FA, such as Example 1.14 `G(Z[1/p])` for `Q`-forms of `SO_5` of `R`-rank 2
  and `Q_p`-rank 1;
- extensions of FM groups by FM groups (Cornulier Prop. 5.4), and groups with a Kazhdan
  homomorphism with dense image onto an FM group (Thm 6.12).

Since amenable quotients are excluded too (item 4), a surviving witness needs a quotient that is
non-amenable, not Kazhdan, and carries an action with an invariant mean and no finite orbit.

## Consequence for the named candidate

For `Γ_p = EL_2(F_p[t,t^-1]) ⋉ F_p[t,t^-1]^2`, item 2 shows that `Γ_p ≤ W(Z)` would force
`SL_2(F_p[t,t^-1]) = EL_2(F_p[t,t^-1])` to lack Property FM. That is the positive-characteristic,
tree-product analogue of the hard case of Cornulier's Conjecture 1.10, which predicts FM. So this
node gives a second, conditional, kill of `Γ_p`, independent of property `(τ)`. It does not decide
`Γ_p` unconditionally.
