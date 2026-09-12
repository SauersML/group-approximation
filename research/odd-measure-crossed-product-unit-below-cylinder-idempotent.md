---
rg: 2
id: odd-measure-crossed-product-unit-below-cylinder-idempotent
kind: claim
title: In the signed Thompson crossed product over odd measures the unit is Murray-von Neumann below the cylinder idempotent
distinct_from:
  ternary-anti-invariant-swap-corner-is-full: that is the corner equation in the whole anti-central summand S_-; this asks for the equivalent subequivalence inside the explicit subalgebra F_3[H] eps_- of the signed Thompson group, a dynamical crossed product, which is sufficient but not necessary.
  ternary-twisted-algebra-has-swap-separated-one-sided-pair: that is an idempotent-free equivalent of the corner equation in all of S_-; this restricts to the signed Thompson crossed product and to the cylinder idempotent q_[0].
artifacts:
  - research/artifacts/ternary-lift-signed-thompson-crossed-product-2026-09-12.md
---

**OPEN.** Let `B = F_3[H] eps_- ~= C(M_-, F_3) ⋊_alg V`, the signed Thompson crossed product over
odd `F_2`-measures (`signed-thompson-algebra-is-odd-measure-crossed-product`). Let `q_[0]` be the
indicator of `{mu([0]) = 1}`. Exhibit `b', c' in B` with

    c' q_[0] b' = eps_- .

By `hadamard-unit-conjugates-swap-idempotent-to-cylinder`, a solution solves
`ternary-anti-invariant-swap-corner-is-full` and refutes Gottschalk on `L_(F_3)(1,2)^x`. The route is
`odd-measure-compression-gives-anti-invariant-corner`.

## Attempts

- **Honest compression, dead.** Lifting the Dirac Hilbert hotel by clopen pieces and `V`-translates
  is excluded by the invariant Haar measure (`odd-measure-space-has-no-honest-thompson-compression`).
  The route `ternary-lift-by-honest-odd-measure-compression` is invalidated.
- **Mod-3 trace, no obstruction.** `Tr(eps_-) = 1` and `Tr(q_[0]) = -1` leave room for an
  equivalent subidempotent of trace `1` (`odd-measure-crossed-product-carries-mod-three-trace`).
- **Intertwiner, dead.** No nonzero finitely supported `v in S_-` intertwines the corner endomorphism
  `iota(g) = s0 g t0 + s1 t1`. Such coefficients are constant on twisted conjugacy orbits in
  `PG = G/<z>`, which are infinite because `G` is simple and `iota(z) != z`. Section 7(b) of the
  artifact.
- **Gate.** If the signed Thompson group `E ⋊ V` is `F_3`-linear sofic, this claim is false
  (`linear-sofic-group-algebra-is-stably-finite`). Soficity of `V` is open.
- **Where it dies.** A witness needs a cover of `M_-` compressible only modulo 3: multiplicities
  `1 mod 3`, with cross terms cancelling mod 3, or equivalently non-function idempotents equivalent
  to `eps_-`. No such cover has been constructed, and no obstruction to one is known. Section 8 of
  the artifact.
