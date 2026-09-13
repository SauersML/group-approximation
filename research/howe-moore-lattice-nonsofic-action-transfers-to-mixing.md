---
rg: 2
id: howe-moore-lattice-nonsofic-action-transfers-to-mixing
kind: claim
title: A lattice in a Howe-Moore group with an ergodic nonsofic action has a free mixing nonsofic action
distinct_from:
  kazhdan-fixed-algebra-blind-to-subgroup-ergodic-actions: that shows no fixed-algebra argument applied to a mixing action can prove it nonsofic; this carries nonsoficity onto a mixing action along an orbit equivalence from a non-mixing one, which that theorem does not cover
  groups-containing-kun-thom-pair-have-nonsofic-actions: that passes nonsoficity to overgroups by co-induction and gives no mixing; this passes it from a lattice to the same lattice through the induced action of a Howe-Moore envelope, which is mixing
  kun-thom-free-nonsofic-action: that is the free nonsofic witness, which is never mixing; this is a transfer theorem producing mixing witnesses from any seed of a Howe-Moore lattice
artifacts:
  - research/artifacts/nonsofic-action-mixing-transfer-2026-09-12.md
  - research/artifacts/nonsofic-action-mixing-transfer-part2-2026-09-12.md
---

**ESTABLISHED (unreviewed).** Let `H` be a second countable locally compact group with the
Howe--Moore property and `Γ <= H` a lattice. Suppose `Γ ↷ (Z,ζ)` is an ergodic p.m.p. action that is
not sofic (Păunescu Definition 1.4). Put `Z' = Z × ({0,1},fair)^Γ` and let `W = H ×_Γ Z'` be the induced
`H`-space. Then the restriction

```text
Γ ↷ W = H ×_Γ Z'
```

is essentially free, **mixing**, and not sofic.

**Dichotomy.** With `sofic-action-with-sofic-ergodic-components-is-sofic`: every lattice `Γ` of a
Howe--Moore group either lies in Păunescu's class `𝒮` or has an essentially free, mixing, nonsofic
p.m.p. action.

**Instances.** `H` can be any group in `howe-moore-property-for-simple-lie-and-p-adic-groups`: for
example `SL_3(Z) <= SL_3(R)`, uniform lattices in `Sp(n,1)`, `SL_3(F_q[t]) <= SL_3(F_q((1/t)))`.
Their finitely generated lattices are linear, hence residually finite and sofic. So a nonsofic action
of any one of them answers `mixing-free-nonsofic-action-of-sofic-group`; see
`mixing-nonsofic-action-from-sl3z-nonsofic-action`.

**Mechanism.** `Ω = H × Z'` is a self-coupling of `Γ` with index `1`. The `Γ`-action on `Ω/Γ = W`
and the `Γ`-action on `Γ\Ω = Γ\H × Z'` are free and orbit equivalent; the latter has `Z` as a factor,
so it is nonsofic. Păunescu Theorem 1.5 moves nonsoficity to `W`, and Howe--Moore makes `W` mixing.
No fixed-point algebra of a Kazhdan subgroup is used, so the blindness theorem does not apply.

**What it does not give.** No lattice of a Howe--Moore group outside `𝒮` is recorded, so no
unconditional mixing example follows. For a *different* lattice of `H`:
`paunescu-class-is-measure-equivalence-invariant` puts all lattices of one lcsc group inside or
outside `𝒮` together, and the dichotomy above then gives each of them a free mixing nonsofic action.
So in a Howe--Moore group, one lattice outside `𝒮` gives every lattice a mixing witness.

Proof in `howe-moore-lattice-nonsofic-action-transfers-to-mixing-proof`.
