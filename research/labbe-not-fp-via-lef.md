---
rg: 2
id: labbe-not-fp-via-lef
kind: route
title: LEF of Labbé's derived full group would refute its finite presentation
target: labbe-shift-derived-full-group-is-not-finitely-presented
requires:
  - labbe-shift-derived-full-group-is-lef
  - minimal-z2-subshift-derived-full-groups-are-fg-simple
  - minimal-aperiodic-wang-shift-exists
---

## Why sufficient

1. **The group.** `Gamma = D([[Z^2 ~ Omega_U]])` is finitely generated, infinite and simple
   (`minimal-z2-subshift-derived-full-groups-are-fg-simple`, applied to
   `minimal-aperiodic-wang-shift-exists`).
2. **If `Gamma` were finitely presented and LEF, it would be residually finite.**
   - Take `Gamma = <S | r_1..r_k>` and a nontrivial `g`. Let `F` be the ball containing `S`, `g`,
     and every prefix of every `r_i`.
   - LEF gives a finite group `Q` and an injective map `phi : F -> Q` that is multiplicative on
     `F`. The `phi(s)` satisfy every `r_i`, since the prefix products stay in `F`.
   - So `phi` extends to a homomorphism `Gamma -> Q` with `phi(g) ≠ 1`.
3. **Contradiction.** An infinite simple group is not residually finite. So LEF
   (`labbe-shift-derived-full-group-is-lef`) forces non-finite presentation.
4. **No false establishment.** The LEF input is OPEN, so this route does not establish its target.
