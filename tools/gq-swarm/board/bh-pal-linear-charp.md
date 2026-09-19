# bh-pal-linear-charp
Direction: T3 LinearHostStatement, characteristic-p half, in Lean (unconditional, Mathlib-only). Prefix GroupApproximation/BooneHigmanLinear/CharP/.
- 09-18 ~14:45 start. Map: the char-p chain `charPLinearHostStatement_of_chain` (ChainCharP) needs coords (proved), absorption (Suslin; open for k >= 2),
  E_N(F_p[s_1..s_k]) f.p. (K2 vanishing; open for k >= 2), affine FP (proved), self-similar host (proved). All open inputs are shared with the bh-met chain and actively worked there: not mine.
- Plan: the unconditional slice k <= 1. One-variable absorption (`specialLinearInElementary_charPPoly_one`, Euclid) + Nagao (`bhNagaoUncond_polynomialFpElementaryFP_le_one`) give:
  (A) GL_M(F_p[s]) embeds in an f.p. self-similar group; (B) every f.g. linear group over a field of char p with trdeg <= 1 over F_p (global function fields, F_q(t), their algebraic extensions) does too.
- 09-18 ~15:45 authored (not landed), in $GQ/work/bh-pal-linear-charp/:
  - CharP/LowTrdegCoords.lean: `exists_polynomialCoordinates_le_trdeg` (Noether normalization of the entry algebra has s <= trdeg_{F_p} K variables), `_le_one`. It rewrites the CharPCoordsAssembly proof (that file uses the nonexistent `Algebra.fg_adjoin_finset`, so it is likely red); it imports only CharPCoordsFree/Away + Coordinates.
  - CharP/OneVariableHost.lean: `embedsInFPSelfSimilarGroup_of_glPoly_le_one`, `LowTrdegCharPLinearHostStatement` + `lowTrdegCharPLinearHost` (NO hypotheses), and the T3 slice `lowTrdegCharP_embedsInFinitelyPresentedSimpleGroup` (LOUD: conditional on FPSelfSimilarEnvelopeStatement).
- UPSTREAM DEPENDENCY (for bh-pal-wire): OneVariableHost's closure (464 modules) contains AbsorptionSuslinEuclidKill and AffineFP{Model,Identities,...}, red at 10:40 and unchanged since. I build on them only through their endpoint theorems; I wait for your repair and do not edit them.
- 09-18 ~16:30 LANDED. The Lean files went in via the coordinator sweep d6f969829 (bytes identical to mine); my fix node went in at 2369945fa. They are UNBUILT.
  - Probe: Slurm job 1325363 stayed PENDING on priority on msismall. Its estimated start was ~22:50, and the whole time it held the fleet-wide msi-build.lock. I cancelled my own job so other lanes are not blocked. Every serialized probe has the same problem while the account's msismall priority is low.
  - Next: re-probe `GroupApproximation.BooneHigmanLinear.CharP.LowTrdegCoords` first (its small closure has no known reds). OneVariableHost waits on bh-pal-wire's EuclidKill / AffineFP repair.
- For bh-pal-surface: a candidate Mathlib-only challenge slice is `∀ p [Fact p.Prime] K [Field K] [Algebra (ZMod p) K], Algebra.trdeg (ZMod p) K ≤ 1 → f.g. H ≤ GL_n(K) → EmbedsInFPSelfSimilarGroup H`. The simple-group version needs the envelope.
