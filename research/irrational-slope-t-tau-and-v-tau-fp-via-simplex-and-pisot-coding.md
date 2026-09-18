---
rg: 2
id: irrational-slope-t-tau-and-v-tau-fp-via-simplex-and-pisot-coding
kind: route
title: T_τ is F_infinity by the full simplex on its breakpoint orbit, and V_τ is finitely presented as a full contracting RSG on the golden-mean shift
target: irrational-slope-t-tau-and-v-tau-are-finitely-presented
requires:
  - circle-pl-groups-inherit-finiteness-from-interval-groups
  - pisot-unit-slope-stein-groups-are-finitely-presented
---

**Proof.**
- **`T_τ`.** `circle-pl-groups-inherit-finiteness-from-interval-groups`, item 2, makes it `F_∞`, from
  `F_∞` of `F_τ`.
- **`V_τ`.**
  - `φ = 1/τ` satisfies `φ² = φ + 1`, so it is a unit with property (F), `Z[φ] = Z[τ]` and `⟨φ⟩ = ⟨τ⟩`.
  - `pisot-unit-slope-stein-groups-are-finitely-presented` makes `V(Z[τ],⟨τ⟩,1)` finitely presented, as a
    full contracting RSG (BBMZ Theorem A).
  - Burillo–Nucinkis–Reeves use left-continuous maps of `(0,1]`. Conjugation by `x ↦ 1 − x` carries them
    to right-continuous maps of `[0,1)`, keeping slopes and the breakpoint set `Z[τ]`. So the two models
    are isomorphic.

`V_τ` is shown finitely presented here, not `F_∞`. Its index-two simple subgroup `V_{xz}` is then a
finitely presented simple group, and so is `T_{xz}`. ∎
