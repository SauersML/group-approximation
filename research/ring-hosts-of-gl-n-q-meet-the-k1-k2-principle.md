---
rg: 2
id: ring-hosts-of-gl-n-q-meet-the-k1-k2-principle
kind: claim
title: The K_1/K_2 principle (MT-B) - Steinberg groups of rings with Q and a Leavitt pair contain every GL_n(Q), while every landed elementary, projective-elementary and unit-quotient form over such rings is infinitely presented
distinct_from:
  rational-scalars-obstruct-fp-elementary-hosts: that is one assembled input, the K_1 obstruction; this is the conjunction of the landed positive Steinberg results and all landed K_1 and K_2 obstructions.
  one-steinberg-group-contains-every-gl-n-q: that is the positive input; this sets it beside the obstructions for the quotient forms.
  gl-n-q-explicit-natural-fp-overgroup: that is Problem 2.7, which the positive half answers; this records why the same rings give no finitely presented simple host in the landed forms.
artifacts:
  - research/artifacts/gq-gq-critic-2.md
---

**ESTABLISHED (assembly)** through `ring-hosts-of-gl-n-q-meet-the-k1-k2-principle-assembly`. The
established part is the conjunction of twelve landed claims, abbreviated from their statements. Each node has
the exact hypotheses, and no new proof is given here. The heuristic reading at the end is **not** claimed.
Source: critic pass 2, `research/artifacts/gq-gq-critic-2.md` §3, MT-B.

## Established part

1. **Steinberg groups, the positive half (G′).**
   - `steinberg-groups-of-fp-rings-are-fp-in-rank-five`: for every finitely presented unital ring `R` and
     every `n >= 5`, `St_n(R)` is finitely presented.
   - `one-steinberg-group-contains-every-gl-n-q`: for any ring `S` that contains `Q` and a binary Leavitt
     pair, the single group `St_4(S)` contains `SL_m(Q)` and `GL_n(Q)` for every `m` and `n`.
   - Through these, `gl-n-q-explicit-natural-fp-overgroup` (Problem 2.7) computes ESTABLISHED.
2. **Quotient forms, the negative half: K_1.**
   - `rational-scalars-obstruct-fp-elementary-hosts`: over a ring `R` containing `Q`, elementary rational
     scalars make `PE_N(R)` and `R^x/Z(R^x)` infinitely presented.
   - `ibn-failure-makes-rational-scalars-elementary`: suppose `R` contains `Q` and `R^m ≅ R^(m+k)`. Then
     `λ^k I_M` is elementary for every `λ` in `Q^x` and every rank `M = m'N` with `m' >= m` and `N >= 2`, so
     those `PE_M(R)` are not finitely presented.
   - `leavitt-scalar-commutators-block-fp-central-quotients`: no unit group of a ring with an infinite central
     field and a Leavitt family is finitely presented modulo its scalars.
3. **Quotient forms, the negative half: K_2.**
   - `infinitely-generated-symbols-block-fp-elementary-groups`: suppose the Steinberg symbols of commuting
     units generate an infinitely generated subgroup of `K_2(R)`. Then no `E_N(R)` with `N >= 3` is finitely
     presented.
   - Two instances:
     - `laurent-rational-symbols-block-fp-elementary-groups`: skew Laurent rings whose base detects rational
       scalars in `K_1`;
     - `matrix-corner-laurent-rings-block-fp-elementary-groups`: matrix rings over `Z`-graded rings with a
       degree-one unit and a commutative or tracial degree-zero part.
   - `full-corners-must-kill-rational-k2-symbols`: if `E_N(R)` is finitely presented and `Q ⊆ R`, then every
     full idempotent corner sends `K_2(Q)` to a finite group.
4. **Specific constructions.**
   - `register-comparison-presentations-are-not-simple`: take a register presentation with a translation
     chain and a finite-fibre comparison between two unbounded registers. It is never simple, whatever
     finitely many base-closure relations are added.
   - `dilation-letters-cannot-divide-the-unit-class`: dilation letters and resolvents cannot make the unit
     class of a one-register-per-type completion divisible by every `n`, unless the top-level matrix is
     singular.
   - `bounded-harmonic-rings-are-not-finitely-presented`: crossed-product rings that get `Q` from one harmonic
     function are not finitely presented and have no finitely presented `E_N`.

## Heuristic reading (not claimed)

- **The slogan.** The critic's slogan is "ring hosts answer G′ but never G".
  - The rational scalars `Q^x` (the `K_1` side) and the Tate symbols of `K_2(Q)` survive as an infinitely
    generated central or elementary obstruction.
  - So a finitely presented simple host would have to contain `SL_n(Q)` through something other than a
    ring's elementary group modulo its centre.
- **What is proved.** Items 2–4 prove this only for the forms `PE_N`, `R^x/Z(R^x)` and `E_N`, under the stated
  hypotheses, and for the three constructions in item 4.
- **What is not claimed.** No finitely presented simple group built from a ring in some other way is excluded.
