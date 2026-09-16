---
rg: 2
id: torsion-free-f-infinity-amenable-non-ea-via-basilica-hnn
kind: route
title: If the Bartholdi–Virág HNN extension of the Basilica group is FP_infinity, it is a torsion-free amenable non-EA group of type F_infinity
target: there-is-torsion-free-f-infinity-amenable-non-ea-group
requires:
  - basilica-hnn-extension-is-fp-amenable-non-ea
  - basilica-group-is-torsion-free-and-contains-every-z-n
  - basilica-hnn-extension-is-fp-infinity
---

Let `B` be the Basilica group, `σ : b ↦ a, a ↦ b^2`, and `B~ = ⟨B, t | t^(−1) g t = σ(g)⟩`.

1. `B~` is finitely presented and amenable, and it is not in `SG`, hence not elementary amenable
   (`basilica-hnn-extension-is-fp-amenable-non-ea`).
2. `B~` is torsion-free (`basilica-group-is-torsion-free-and-contains-every-z-n`, item 5). Every
   element is `t^p g t^(−q)` with `g ∈ B`. A torsion element lies in `ker χ`, where `χ(t) = 1`, so
   it is conjugate to an element of the torsion-free group `B`.
3. Suppose `B~` is of type `FP_∞` (`basilica-hnn-extension-is-fp-infinity`). Then it is of type
   `F_∞`, because a finitely presented group of type `FP_∞` over `Z` is of type `F_∞`. Take a
   finite presentation complex, and at each stage kill the finitely generated `π_n = H_n` of the
   universal cover of the `n`-skeleton.
4. So `B~` is a torsion-free amenable group of type `F_∞` that is not elementary amenable.

**Where the answer would sit.**

- `B~` contains `Z^n` for every `n` (item 3 of the torsion-free claim), so `cd B~ = ∞`. It falls
  in the second case of the target's dichotomy: if Thompson's `F` is non-amenable, `B~` omits `F`.
- By the Kropholler fence recorded in `basilica-hnn-extension-is-fp-infinity`, the third premise
  forces `B ∉ H𝔉`.

The third premise is open, so this route does not establish its target.
