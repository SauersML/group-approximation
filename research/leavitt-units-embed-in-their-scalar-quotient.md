---
rg: 2
id: leavitt-units-embed-in-their-scalar-quotient
kind: claim
title: The binary Leavitt unit group embeds in its own quotient by the scalars through a corner homomorphism
distinct_from:
  odd-leavitt-unit-groups-mod-scalars-are-fp-simple: that is finite presentability and simplicity of the quotient by the scalars; this is an explicit embedding of the unit group itself into that quotient, which transports nonsoficity and nonsurjunctivity upward.
artifacts:
  - research/artifacts/invariant-output-descent-and-sensitivity-2026-09-12.md
---

Let `k` be a field, `R = L_k(1,2)`, `G = R^x` and `Z = k^x`, the central scalars.
Then

    iota(g) = s0 g t0 + s1 t1

is an injective homomorphism `G -> G` with `iota(G) ∩ Z = {1}`. So the composite
`G -> G -> G/Z` is injective: the quotient by the scalars contains a copy of the
unit group.

*Proof.* The cross terms vanish because `t0 s1 = t1 s0 = 0`, so
`iota(g) iota(h) = s0 g h t0 + s1 t1 = iota(gh)`, and `iota(1) = 1`. Also
`t0 iota(g) s0 = g`, so `iota` is injective. If `iota(g) = lambda` with `lambda` in
`k^x`, then `iota(g) s1 = s1` gives `(lambda - 1) s1 = 0`, and `t1 s1 = 1` forces
`lambda = 1`, hence `g = 1`. QED
