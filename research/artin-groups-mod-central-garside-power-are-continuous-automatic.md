---
rg: 2
id: artin-groups-mod-central-garside-power-are-continuous-automatic
kind: claim
title: Modulo a central power of its Garside element, a finite-type Artin group is continuous automatic, with normal forms the positive Deligne forms having fewer leading Delta letters than that power
distinct_from:
  spherical-artin-groups-satisfy-boone-higman: that is Boone--Higman for the Artin groups themselves; this is a continuous automatic structure, in the sense of Belk--Bleak--Chatterji--Matucci--Perego, on their quotients by central Garside powers, such as B_n modulo its center.
  artin-normal-form-boundary-full-groups-fix-a-point: that finds a global fixed point, Delta^{-infinity}, on the Deligne normal-form boundary of the Artin group; the quotient language here has no Delta^{-1} letters, so that point is absent from its boundary.
  low-complexity-mapping-class-groups-are-continuous-automatic: that is the application to mapping class groups of punctured spheres and genus two; this is the Garside lemma it uses.
artifacts:
  - research/artifacts/gq-bh-bh-hhg-bbmz-method-for-hhgs.md
---

**ESTABLISHED** (lane proof, not reviewed; no priority claimed). Proof:
`artin-mod-central-garside-continuous-automatic-proof`.

## Setting

Belk--Bleak--Chatterji--Matucci--Perego (BBCMP), *Rational embeddings of continuous
automatic groups* (preliminary version, PDF in `gq/src/bbcmp/`, §1.1 and §2.1).
- A language of normal forms `L ⊆ X^*` has exactly one word for each element.
- `L` is *continuous* if the left action extends continuously to `L ∪ ∂L`. Their
  Proposition 2.1 criterion: for each monoid generator `s` and each `N` there is `M` with
  `|g ∧ h|_L ≥ M ⇒ |sg ∧ sh|_L ≥ N`.
- An *automatic structure*, in their convention, is a regular `L` with `π(L) = G` such
  that each `R_x = {(α,β) : π(α) = x π(β)}` is synchronous rational.
- `G` is *continuous automatic* if some automatic structure is a continuous normal form.

`A` is an Artin group of finite type, `A^+` its positive monoid, and `Δ` the Garside
element. Let `c ∈ {1, 2}` with `z = Δ^c` central. `Δ^2` is always central, and `Δ` is
central exactly when conjugation by `Δ` is trivial.

## Statement

Let `Ā = A/⟨z⟩` and `X = (1, Δ]`, the nontrivial left divisors of `Δ`. Let

    L̄ = { Δ^p x_1 ⋯ x_k : 0 ≤ p < c, k ≥ 0, x_i ∈ (1,Δ), x_1 → x_2 → ⋯ → x_k },

where `x → y` means `pref(xy) = x`, as in BBCMP §2.3. Then:
1. `L̄` maps bijectively onto `Ā`. The word for `ḡ` is the left-greedy form of the unique
   lift `g` of `ḡ` with `inf(g) ∈ {0, …, c−1}`.
2. `(X, L̄)` is an automatic structure on `Ā`, in the BBCMP convention.
3. `L̄` is a continuous normal form.

So `Ā` is continuous automatic. In particular, `B_n/Z(B_n) = B_n/⟨Δ^2⟩` is continuous
automatic for every `n ≥ 2`.

## Scope

- The words of `L̄` contain no `Δ^{-1}`. So the global fixed point `Δ^{-∞}` of
  `artin-normal-form-boundary-full-groups-fix-a-point` is not a point of `∂L̄`. Nothing
  else is claimed about fixed points or faithfulness on `∂L̄`.
- Several Garside inequalities and closure facts for automatic structures are recalled
  from the standard literature, not re-derived. They are listed in the proof route.
