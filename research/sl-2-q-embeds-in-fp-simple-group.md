---
rg: 2
id: sl-2-q-embeds-in-fp-simple-group
kind: claim
title: SL_2(Q) embeds in a finitely presented simple group
distinct_from:
  psl2-q-embeds-in-fp-simple-group: that is the simple quotient PSL_2(Q) = SL_2(Q)/{±I}, which is not a subgroup of SL_2(Q); this is SL_2(Q) itself, with its centre, which the Mobius device of pgl2-q-in-rover-nekrashevych-group-of-rational-iwahori cannot reach.
  gl-n-q-embeds-in-fp-simple-group: that root is GL_n(Q) for every n >= 2 and implies this; this is the rank-one stepping stone, which is not known to imply the root.
  sl-odd-q-simple-inputs-for-gl-n-q-root: that reduces the root to the simple groups SL_m(Q) with m odd; SL_2(Q) is not simple and does not contain GL_n(Q) for any n >= 2.
---

**OPEN.** There is a finitely presented simple group containing `SL_2(Q)`.

**Position.**
- **Implied by the root.** `SL_2(Q) <= GL_2(Q)`, so
  `gl-n-q-embeds-in-fp-simple-group` implies this (route `sl-2-q-via-gl-n-q`).
- **A named stepping stone** of the gq swarm (with `Aff(Q)`, `U_3(Q)`,
  `GL_2(Q)`). It contains the divisible group `(Q,+)`, so it has no residually
  finite overgroup (O1 of the root). `V` contains no `(Q,+)` (O3). `SL_2(Q)`
  contains the distorted cyclic subgroups of `BS(1,4)` (`diag(2,1/2)` conjugates
  a unipotent `u` to `u^4`), so O4 applies as well. O2 concerns `SL_3(Z)` and
  does not apply.
- **Tree structure.** For every prime `l`, `SL_2(Q) = A *_{Γ_0(l)} A^α` with
  `A = SL_2(Z_(l))` (`sl-2-q-is-an-amalgam-of-sl-2-z-localized-at-ell`).
  `sl-2-q-via-hecke-overgroup-and-bliw` derives this claim from the
  residually-finite-world hypothesis `sl-2-z-localized-has-fp-hecke-overgroup`
  and Bux--Llosa Isenrich--Wu Theorem C.

## Attempts

None beyond the two routes above.
