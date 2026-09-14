# sk-lef-action ledger

Note: `simple_kazhdan_sofic_group.tex` at origin/main 37551fd93 (md5 b55c0d23…, census 649cb1f80).
Scope (coordinator, 23:15): "The ring and property (T)" (tex 131–149) at Λ generality; the lamplighter
material in the LEF-groups proof (tex 356–368); and, absorbing sk-lef-models (which left no drafts or
report), the finite models making `R_Δ` matricial (tex 370–391).

## CLAIM
CLAIM crossed product for group actions GroupApproximation/Dynamics/ClopenGroupCrossedProduct.lean
CLAIM printed ring and property (T) GroupApproximation/Manuscript/SimpleKazhdanSofic/GeneralRingPropertyT.lean
CLAIM lamplighter action (tex 356–368) GroupApproximation/Manuscript/SimpleKazhdanSofic/LamplighterAction.lean
CLAIM lamplighter finite models (tex 370–391) GroupApproximation/Manuscript/SimpleKazhdanSofic/LamplighterModels*.lean

Ownership check (23:40): no group-action crossed product on origin, in the shared tree or in any
`lanes/*.files`; the Simplicity drafts are all stated over `ℤ` (`ClopenCrossedProduct T`); the only
matricial spelling is ms-core-3's `IsMatricialLEFRing` (FiniteModelsGroup), not thm:general's φ_k.
Not mine: tex 396–402 (diag(u_ξ,1,1), ms-intro-2's `LEFDiagonalCommutators`), the application of
thm:general (sk-lef-assembly, ct-two-ended).

## State 10:20 (tip 8b36733d7, md5 29d63f79…, census 9cb80166d)

Scope: the group-action crossed product, the lamplighter action and ring, the absorbed finite models
(sk-lef-models left no drafts), and the concrete host `LamplighterHostStatement` (sk-lef-assembly, 0da57c90d).
ct-involution took module B (`GeneralRingPropertyT`) and its rows at 20:35.

| module | tex (8b36733d7) | state |
|---|---|---|
| `Dynamics/ClopenGroupCrossedProduct` | 134–137 | GREEN 0914-083028-22533, on origin 1fda53034, wire-queued |
| `SimpleKazhdanSofic/LamplighterAction` | 105–106, 356–366 | GREEN 0914-084237-64298, 407f74f33, wire-queued |
| `SimpleKazhdanSofic/LamplighterRing` | 366–369 | GREEN 0914-085103-16892, ecfb81908, wire-queued |
| `SimpleKazhdanSofic/LamplighterModelSequence` | 371–374 | GREEN 0914-085103-16892, ecfb81908, wire-queued |
| `SimpleKazhdanSofic/LamplighterModelAction` | 374–379 | GREEN 0914-091346-7548, a780741a0, wire-queued |
| `SimpleKazhdanSofic/LamplighterModelMatrices` | 379–389 | GREEN 0914-092100-55675, eaeed6d23, wire-queued |
| `SimpleKazhdanSofic/LamplighterModelGeneration` | 389–392 | GREEN 0914-100806-41365, 7709d7bfe, wire-queued |
| `SimpleKazhdanSofic/LamplighterHost` | 392–403 | fixes landed unverified 4e0c613ce; probe pending (the 10:14 probe lost its MSI hop) |

`LamplighterHost` proves `isMatricialVia_lampRing` (the reindexed `φ_n` on the printed generators), applies
ct-two-ended's closed `printedSimpleKazhdanGeneral` (`isLEFHost_lampRing`, with block flattening to
`SL_{3N}(F₂)`), embeds `[Δ,Δ]` through ms-intro-2's `lefDiagonalHom` (`exists_commutator_embedding`), and
states `PrintedLamplighterHost`, which is `LamplighterHostStatement` word for word. sk-lef-assembly's
`LEFCharacterizationClosed` consumes it as `lamplighterHostStatement := printedLamplighterHost`.

## Rows (metadata/sk-census-rows/sk-lef-action.tsv)

| key | tex | carrier | status |
|---|---|---|---|
| fb6f6f03c19a | 356–359 | `printedLamplighterAffineGroup` | formalized (re-keyed from ed367be4322a) |
| 9b414612d181 | 359–360 | `printedLamplighterAffineGroup`, `printedLamplighterMinimalTopologicallyFree` | formalized |
| ac91c158ed24 | 360–362 | `printedLamplighterMinimalTopologicallyFree` | formalized (re-keyed from d93c07e63a40) |
| a8760ee6d3af | 362–365 | `printedLamplighterMinimalTopologicallyFree` | formalized (re-keyed from 4337251611d4) |
| 2bcb951d302e | 365–366 | `printedLamplighterMinimalTopologicallyFree` | formalized |
| ee8c6f26a1da | 366–369 | `printedLamplighterRingGeneration` | formalized |
| bd0a4c539428 | 371–374 | `printedLamplighterBallModels` | formalized |
| e1aa5c966b58 | 374–377 | `printedLamplighterModelAction` | formalized (re-keyed from dccd78f118a7) |
| 096f124abe31 | 377–379 | `printedLamplighterModelAction` | formalized |
| c78a4854489a, cdb7675d1521, ba51377f43f6, 472c3d5ac00b | 379–389 | `printedLamplighterModelMatrices` | formalized |
| 814c69fe374e | 389–392 | `printedLamplighterMatricial` | formalized |
| 358e51e6a815 | 392–395 | `isLEFHost_lampRing`, `printedLamplighterHost` | held by skf-consequences (partial); carrier to be sent after the host is green |
