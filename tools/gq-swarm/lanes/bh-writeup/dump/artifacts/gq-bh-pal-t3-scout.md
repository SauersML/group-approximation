# T3 scout: Lean coverage of "every f.g. linear group over any field embeds in an f.p. simple group"

Lane `bh-pal-t3-scout`, 2026-09-18. Report only: no builds, no Lean written. Read at origin/main
fb1c469c2 (09:13 CDT). Target node: `finitely-generated-linear-groups-satisfy-boone-higman`.
Lean target: `GroupApproximation.BooneHigman.FinitelyGeneratedLinearStatement` (T3), already
defined Mathlib-only in `GroupApproximation/BooneHigman/Statement/Basic.lean`.

## Headline

**T3 is already a sub-goal of the other session's metabelian chain, and almost all of it is on
disk.** `Products.finitelyGeneratedLinearStatement_of_hosts` (`BooneHigman/Products/Hosts.lean`)
derives T3 from `Products.LinearHostStatement` and `Products.FPSelfSimilarEnvelopeStatement`.
Both are exactly the linear-host and envelope halves of the metabelian root. So T3 needs
**no new host in a new directory**. It needs:
- one thin wiring theorem, about 50 lines;
- the same six open gap Statements the metabelian root still needs.

A separate `GroupApproximation/BooneHigmanLinear/` char-0 or char-p host, as the plan proposes,
would duplicate proved modules: `CharZeroHost/**`, `CharPHost/**`, `ChainWiredAffine`, and the
coordinate assemblies.

## Step-by-step coverage

| # | Informal step | Lean statement | Status on main |
|---|---|---|---|
| 1a | Char 0 coordinates: f.g. H ≤ GL_n(K) ↪ GL_M(ℤ[1/m][t_0..t_{k-1}]) | `Chain.CharZeroPolynomialCoordinatesStatement` ← `CharZeroHost.coordinatesStatement_of_fgSubring` ∘ `fgSubringCoordinates` (`CharZeroCoordsAssembly.lean:42`) | **Proved** |
| 1b | Char p coordinates: ↪ GL_M(F_p[s]) | `CharPCoords.CharPPolynomialCoordinatesStatement` = `charPPolynomialCoordinates` (`CharPCoordsFreeClosed.lean:22`) | **Proved** |
| 2 | Absorption GL_M(S) ↪ E_N(S) via diag(g, g⁻ᵀ, 1) and Suslin SL_N = E_N | `Absorption.charZero/charPElementaryAbsorptionStatement_of_suslin` from `PolynomialSuslinStatement` ← `suslinOneVariable_of_patching` ← `suslinPatching_of_localHorrocks` | **OPEN: `Absorption.SuslinLocalHorrocksStatement`** |
| 3p | E_N(F_p[s]) f.p. (N ≥ k+4) | `ElemFP.PolynomialFpElementaryFPStatement` ← K₂ vanishing ← (`hdiag`, `hone`, `hfield`) | `hfield`: **proved** (`bruhatBigCell`, `ElemFPFieldK2BruhatBigCellEndpoint.lean:111`). **OPEN: `ElemFP.VdKRowExtensionStatement`** (for `hdiag`) and **`ElemFP.PolyK2CubeNilLocalStatement`** (for `hone`) |
| 3z | E_N(ℤ[1/m][t]) f.p. | `charZeroElementaryFPFive_of_stableK2FG` ← `CharZeroStableK2FGStatement` ← `charZeroStableK2FG_of_basePos_of_cubeGapPos` | **OPEN: `ElemFPCharZero.CharZeroK2PosStabGenStatement`** and **`ElemFPCharZero.CharZeroK2CubeGapPosStatement`** |
| 4 | Affine extension R^N ⋊ E_N(R) f.p. | `AffineExtensionFPStatement` = `affineExtensionFPStatement_holds` (`ChainWiredAffine.lean:54`) | **Proved** |
| 5 | Parameter-coordinate self-similar faithful action | `charZeroAffineSelfSimilarStatement` (`CharZeroHost/Endpoint.lean:54`), `charPAffineSelfSimilarStatement_holds` (`CharPHost/TreeHost.lean:107`) | **Proved** |
| 5′ | f.p. group + faithful self-similar rep ⇒ `EmbedsInFPSelfSimilarGroup` | `Products.embedsInFPSelfSimilarGroup_of_rep`, `embedsInFPSelfSimilarGroup_of_affineHost` | **Proved** |
| 6 | Zaremsky Thm 1.1: f.p. self-similar ⇒ f.p. simple (Röver–Nekrashevych) | `FPSelfSimilarEnvelopeStatement` ← `fpSelfSimilarEnvelope_of_frontier'` from `hV`, `hcore`, `hfi`, `hw`; simplicity is `rnCommutatorSimpleStatement_holds` | `hw`: **proved** (`rnWreathEmbed`). `hfi`: **proved** via `rnFiniteIndex_of_vPerfect genTorsionVPerfect` (`EnvelopeVPerfect.lean:99`). `hcore`: **proved** from `rnNF_finiteCore` (`EnvelopeRelatorsNormalFormFinal.lean:220`) plus Higman's V f.p. **OPEN: `Envelope.HigmanVSwapSectionStatement`**, which feeds both `hV` and V's finite presentation inside `hcore` |
| 7 | T3 from 1–6 | `Products.finitelyGeneratedLinearStatement_of_hosts` (`Products/Hosts.lean:42`) | **Proved** (composition) |

## The exact T3 frontier: 6 Statements, all shared with the metabelian root

1. `Absorption.SuslinLocalHorrocksStatement`: Horrocks, the local case of Quillen–Suslin. Estimate 2–5 kLOC.
2. `ElemFP.VdKRowExtensionStatement`: van der Kallen injective stability for K₂. It is logically
   stronger than the `hdiag` it replaces. Estimate 3–8 kLOC; about 50 `VdK*.lean` files are already
   in progress.
3. `ElemFP.PolyK2CubeNilLocalStatement`: equivalent to `hone`. Estimate 1–3 kLOC.
4. `ElemFPCharZero.CharZeroK2PosStabGenStatement`: base generation for char-0 stable K₂. Estimate 2–4 kLOC.
5. `ElemFPCharZero.CharZeroK2CubeGapPosStatement`: equivalent to `CharZeroK2NilGapStatement`. Estimate 2–4 kLOC.
6. `Envelope.HigmanVSwapSectionStatement`: Higman's V finite presentation, swap section. Estimate 1–3 kLOC.

The metabelian root (`finitelyPresentedMetabelianStatement_of_frontierThree`) takes the same six,
plus `Coprimary.PureCharPrimeEHighModuleStatement`. That seventh one now has a hypothesis-free
theorem on disk (`eHighWittE_pureCharPrimeEHighModule`, `PureCharPrimeEHighWittEWire.lean:90`).
So **T1, T2 and T3 share one frontier.** Closing the six closes all three, up to build status.

## Build status caveats

- Nothing under `GroupApproximation/BooneHigman/**` is imported by the root
  `GroupApproximation.lean`, which has 0 BooneHigman imports. The `GroupApproximation` lean_lib has
  no explicit roots. So these modules are **not** in the default build or root CI. Their green
  status rests on the other session's MSI builds.
- Many recent commits are "WIP: swarm-authored Lean in flight (uncompiled)". Every "Proved" cell
  above means "a hypothesis-free theorem exists on main", not "a trusted build of it is green".
  A trusted `scripts/remote-build.sh` build of the proved leaves is needed before the megapair
  cites them.
- No T3 wiring theorem exists yet. The only consumer of `finitelyGeneratedLinearStatement_of_hosts`
  is its own file.

## Activity on the six gaps (other session, last 24 h, commit subjects)

Suslin/Horrocks 35, Higman/V 28, van der Kallen 21, char-0 K₂ 13, cube/nil 11. Every gap is under
active bh-met-* work. Extra builders on the same gap risk collisions (same-path clobber) and
duplicated lemmas.

## Recommended split (in place of BooneHigmanLinear/ hosts)

- **bh-pal-t3-assembly**, small, ours: new file
  `GroupApproximation/BooneHigmanLinear/FrontierWiring.lean` with
  `finitelyGeneratedLinearStatement_of_frontierThree (hH hvdk hloc hgen hcube hswap)`, about 50
  lines. It composes `finitelyGeneratedLinearStatement_of_hosts`, `linearHostStatement_of_frontier`
  (with `bruhatBigCell`, `fgSubringCoordinates` plugged in) and `fpSelfSimilarEnvelope_of_frontier'`
  (with `rnNF_finiteCore`, `genTorsionVPerfect`, `rnWreathEmbed`). It mirrors
  `ChainWiredFrontierThree`. It feeds the megapair's T3 theorem through bh-pal-surface. One trusted
  MSI build of this file and its imports also checks that the "Proved" leaves compile.
- **Builders**: no new char-0 or char-p host. Put extra hands on the least-covered shared gaps,
  coordinated with the owning session by reading commit logs and messaging it:
  - char-0 builder → gaps 4–5 (`CharZeroK2PosStabGen`, `CharZeroK2CubeGapPos`);
  - char-p builder → gap 3 (`PolyK2CubeNilLocal`), which has the least activity.
  - Leave gaps 1, 2 and 6 (Suslin, van der Kallen, Higman V) to the bh-met lanes, which have the
    most momentum there.
  - Each builder owns new files only (for example under `GroupApproximation/BooneHigmanLinear/Gaps/`)
    and proves the gap Statement by name. It must not edit bh-met files unless the owner agrees.
