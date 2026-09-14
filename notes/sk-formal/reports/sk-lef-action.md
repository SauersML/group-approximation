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

## State 09:05 (after the 08:28 reboot; tip 696c4b602, md5 0648e5f8…, census aa6f988f4)

Scope after the coordinator's 20:35 split: ct-involution took module B (`GeneralRingPropertyT`) and its rows. This
lane keeps the group-action crossed product, the lamplighter action and ring, and the absorbed finite models
(sk-lef-models left no drafts), aiming at `LEFLamplighterStatement` (sk-lef-assembly's LEFCharacterization).

| module | tex | state |
|---|---|---|
| `Dynamics/ClopenGroupCrossedProduct` | 134–137 | GREEN 0914-083028-22533, on origin 1fda53034, wire-queued |
| `Manuscript/SimpleKazhdanSofic/LamplighterAction` | 105–106, 384–393 | GREEN 0914-084237-64298, LANDED 407f74f33, wire-queued |
| `Manuscript/SimpleKazhdanSofic/LamplighterRing` | 393–396 | GREEN 0914-085103-16892, on origin ecfb81908, wire-queued |
| `Manuscript/SimpleKazhdanSofic/LamplighterModelSequence` | 398–401 | GREEN 0914-085103-16892, on origin ecfb81908, wire-queued |
| `Manuscript/SimpleKazhdanSofic/LamplighterModelAction` | 401–406 | probing |
| `Manuscript/SimpleKazhdanSofic/LamplighterModelMatrices` | 406–416 | written, unverified |
| generation of `M_{2^{|Q'_n|}}(F₂)` and `IsMatricialVia` | 416–419 | next |
| application of thm:general, `LEFLamplighterStatement` | 419–422 | over ct-two-ended's `PrintedSimpleKazhdanGeneral` (40cf3ae5b) and skf-consequences' LamplighterSimplicity |

Spelling agreements: ct-two-ended states thm:general over `ClopenGroupCrossedProduct` with `MulAction`,
`MulAction.IsMinimal` and inline freeness (definitionally `IsTopologicallyFreeAction`); skf-consequences proves
simplicity of `EL_n(LampRing Δ)` in `LamplighterSimplicity`.

## Rows (metadata/sk-census-rows/sk-lef-action.tsv, landed 088a229c9)

| key | tex | carrier | status |
|---|---|---|---|
| ed367be4322a | 384–386 | `printedLamplighterAffineGroup` | formalized |
| 9b414612d181 | 386–388 | `printedLamplighterAffineGroup`, `printedLamplighterMinimalTopologicallyFree` | formalized |
| d93c07e63a40 | 388–389 | `printedLamplighterMinimalTopologicallyFree` | formalized |
| 4337251611d4 | 389–392 | `printedLamplighterMinimalTopologicallyFree` | formalized |
| 2bcb951d302e | 392–393 | `printedLamplighterMinimalTopologicallyFree` | formalized |
| ee8c6f26a1da | 393–396 | `printedLamplighterRingGeneration` | formalized |
| bd0a4c539428 | 398–401 | `printedLamplighterBallModels` | formalized |
| dccd78f118a7, 096f124abe31 | 401–406 | `printedLamplighterModelAction` | pending probe |
| c78a4854489a, cdb7675d1521, ba51377f43f6, 472c3d5ac00b | 406–416 | `printedLamplighterModelMatrices` | pending probe |
| 814c69fe374e, 358e51e6a815 | 416–422 | generation, thm:general application | open |
