---
id: fix-boone-higman-linear-char-p-one-variable-host
kind: claim
rg: 2
title: "Fix BooneHigmanLinear.CharP.OneVariableHost: red imports (Euclid Suslin step, affine FP) block the unconditional trdeg <= 1 char-p linear host"
---

Recorded against `char-p-linear-groups-satisfy-permutational-boone-higman` (it was a route with no prerequisites listed, which the checker would read as a complete proof of `char-p-linear-groups-satisfy-permutational-boone-higman`).

**Modules.** `GroupApproximation/BooneHigmanLinear/CharP/OneVariableHost.lean` and its coordinates file
`GroupApproximation/BooneHigmanLinear/CharP/LowTrdegCoords.lean` (lane `bh-pal-linear-charp`, landed
unbuilt under the 09-18 "everything on main, red OK" order). Neither is root-imported.

**What they state (no hypotheses).**
- `exists_polynomialCoordinates_le_trdeg`: a finitely generated `H ≤ GL_n(K)`, `K` a field over `F_p`,
  embeds in `GL_M(F_p[x_0..x_{s-1}])` with `s ≤ trdeg_{F_p} K`. The Noether normalization of the entry
  algebra has at most `trdeg` variables.
- `embedsInFPSelfSimilarGroup_of_glPoly_le_one`: a group inside `GL_M(F_p[s_0..s_{k-1}])` with `k ≤ 1`
  embeds in a finitely presented self-similar group. It uses the one-variable Suslin step
  `specialLinearInElementary_charPPoly_one` (Euclid), Nagao's `bhNagaoUncond_polynomialFpElementaryFP_le_one`,
  `affineExtensionFPStatement_holds` and `charPAffineSelfSimilarStatement_holds`.
- `lowTrdegCharPLinearHost : LowTrdegCharPLinearHostStatement`: every finitely generated linear group
  over a field with `trdeg_{F_p} K ≤ 1` (finite fields, `F_q(t)`, global function fields, their algebraic
  closures) embeds in a finitely presented self-similar group. This is the `trdeg ≤ 1` slice of
  `Chain.CharPLinearHostStatement`, with no gap Statement.
- `lowTrdegCharP_embedsInFinitelyPresentedSimpleGroup`: the matching slice of T3. It is conditional on
  `Products.FPSelfSimilarEnvelopeStatement` alone.

**First error.** No build yet. The trusted probe (Slurm job 1325363, msismall) was still PENDING on
priority at 16:25 CDT. The status is unknown, not green.

**Inputs (nearest red imports).** `fix-bhmet-elem-fpk2-poly-deg-const`, `fix-bhmet-elem-fpnk2-core-slice`, `fix-bhmet-vd-k-row-ext-field`, `fix-boone-higman-linear-char-p-low-trdeg-coords`. Fix those first: errors here may be knock-on.

**What it needs.**
1. Its closure (464 modules) contains modules that were red at 10:40 and are unchanged since:
   `BooneHigman.Metabelian.AbsorptionSuslinEuclidKill` and `BooneHigman.Metabelian.AffineFP{Model,Identities}`
   (bh-pal-wire's red list, `$GQ/board/bh-pal-wire.md`). They have no fix nodes yet, and bh-pal-wire owns
   their repair. This node consumes them only through the endpoint theorems named above.
2. Any errors in the two new files themselves, which will be known once the probe runs.

`requires:` is left empty because the red imports have no fix nodes yet. Add them here when they exist.

**Why it matters.** It is the largest unconditional piece of the T3 linear host in positive
characteristic. The general case `k ≥ 2` still needs `SuslinLocalHorrocks`, `VdKRowExtension` and
`PolyK2CubeNilLocal` (the shared frontier-three gaps).
