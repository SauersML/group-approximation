# FIX GRAPH index (Cairn fix nodes research/fix-*.md). Owner: fix-graph-lead. One line: <status> <node-id> <module> <owner-lane>
# Source: trusted MSI build of origin/main 3c8b417428 (error index work/bh-pal-integrate/scratch/errindex-3c8b417428.txt). Nodes 3b413a74c; dedupe 4edcbf1ee (16:3x).
# All 32 are leaves in that build (no red imports). Their importers did not build, so more reds will surface once these are fixed; they get new nodes with requires-edges.
# BH repairs: bh-pal-wire has repairs in its work dir for all 27 (FrontierFour probe queued). SK: ms-green-sk.

## Open
OPEN fix-bhmet-envelope-cantor-action GroupApproximation.BooneHigman.Metabelian.EnvelopeCantorAction bh-pal-wire
OPEN fix-bhmet-envelope-higman-v-gen-family GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVGenFamily bh-pal-wire
OPEN fix-bhmet-envelope-higman-v-swap-gen-all GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVSwapGenAll bh-pal-wire
OPEN fix-bhmet-affine-fp-identities GroupApproximation.BooneHigman.Metabelian.AffineFPIdentities bh-pal-wire
OPEN fix-bhmet-envelope-gen-torsion-nakayama GroupApproximation.BooneHigman.Metabelian.EnvelopeGenTorsionNakayama bh-pal-wire
OPEN fix-bhmet-pure-char-prime-e-high-coprimary-fp GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighCoprimaryFp bh-pal-wire
OPEN fix-bhmet-torsion-free-coprimary-block GroupApproximation.BooneHigman.Metabelian.TorsionFreeCoprimaryBlock bh-pal-wire
OPEN fix-sk-leavitt-k2-field-two-action GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwoAction ms-green-sk
OPEN fix-bhmet-coprimary-module GroupApproximation.BooneHigman.Metabelian.CoprimaryModule bh-pal-wire
OPEN fix-bhmet-pure-char-prime-e-high-witt-e-coeff GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittECoeff bh-pal-wire
OPEN fix-sk-sk-rows-steinberg-weyl-diagonal GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.SteinbergWeyl.Diagonal ms-green-sk
OPEN fix-bhmet-char-p-host-tree-word GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeWord bh-pal-wire
OPEN fix-bhmet-char-zero-host-letters GroupApproximation.BooneHigman.Metabelian.CharZeroHost.Letters bh-pal-wire
OPEN fix-bhmet-char-p-host-carry-recursion GroupApproximation.BooneHigman.Metabelian.CharPHost.CarryRecursion bh-pal-wire
OPEN fix-bhmet-pure-char-prime-e-high-witt-e-base GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittEBase bh-pal-wire
OPEN fix-bhmet-affine-fp-model GroupApproximation.BooneHigman.Metabelian.AffineFPModel bh-pal-wire
OPEN fix-bhmet-char-p-coords-free-mul GroupApproximation.BooneHigman.Metabelian.CharPCoordsFreeMul bh-pal-wire
OPEN fix-bhmet-pure-char-zero-matrix GroupApproximation.BooneHigman.Metabelian.PureCharZeroMatrix bh-pal-wire
OPEN fix-bhmet-char-p-coords-assembly GroupApproximation.BooneHigman.Metabelian.CharPCoordsAssembly bh-pal-wire
OPEN fix-bhmet-pure-char-prime-e-base GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEBase bh-pal-wire
OPEN fix-bhmet-pure-char-zero-cocycle GroupApproximation.BooneHigman.Metabelian.PureCharZeroCocycle bh-pal-wire
OPEN fix-sk-leavitt-k2-padded-central-matrix-id GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.MatrixId ms-green-sk
OPEN fix-sk-leavitt-k2-row-column-vec-prod GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.RowColumn.VecProd ms-green-sk
OPEN fix-bhmet-torsion-free-noether-localize GroupApproximation.BooneHigman.Metabelian.TorsionFreeNoetherLocalize bh-pal-wire
OPEN fix-bhmet-pure-char-prime-e-high-artin-hasse-alg GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighArtinHasseAlg bh-pal-wire
OPEN fix-bhmet-envelope-finite-index-abel GroupApproximation.BooneHigman.Metabelian.EnvelopeFiniteIndexAbel bh-pal-wire
OPEN fix-bhmet-absorption-suslin-euclid-kill GroupApproximation.BooneHigman.Metabelian.AbsorptionSuslinEuclidKill bh-pal-wire
OPEN fix-sk-leavitt-k2-padded-central-vectors GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.Vectors ms-green-sk
OPEN fix-bhmet-char-zero-coords-denominators GroupApproximation.BooneHigman.Metabelian.CharZeroCoordsDenominators bh-pal-wire
OPEN fix-bhmet-elem-fp-char-zero-k2-split GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2Split bh-pal-wire
OPEN fix-bhmet-elem-fpk2-stab-diag-endpoint GroupApproximation.BooneHigman.Metabelian.ElemFPK2StabDiagEndpoint bh-pal-wire
OPEN fix-bhmet-elem-fpk2-local-quillen-ideal GroupApproximation.BooneHigman.Metabelian.ElemFPK2LocalQuillenIdeal bh-pal-wire

## Superseded duplicates (fix-bh-a, 4160e3e2d); track only the survivor
SUPERSEDED fix-bh-met-absorption-suslin-euclid-kill -> fix-bhmet-absorption-suslin-euclid-kill
SUPERSEDED fix-bh-met-affine-fp-identities -> fix-bhmet-affine-fp-identities
SUPERSEDED fix-bh-met-affine-fp-model -> fix-bhmet-affine-fp-model
SUPERSEDED fix-bh-met-char-p-coords-assembly -> fix-bhmet-char-p-coords-assembly
SUPERSEDED fix-bh-met-char-p-coords-free-mul -> fix-bhmet-char-p-coords-free-mul
SUPERSEDED fix-bh-met-char-p-host-carry-recursion -> fix-bhmet-char-p-host-carry-recursion
SUPERSEDED fix-bh-met-char-p-host-tree-word -> fix-bhmet-char-p-host-tree-word
SUPERSEDED fix-bh-met-char-zero-coords-denominators -> fix-bhmet-char-zero-coords-denominators
SUPERSEDED fix-bh-met-char-zero-host-letters -> fix-bhmet-char-zero-host-letters
SUPERSEDED fix-bh-met-coprimary-module -> fix-bhmet-coprimary-module
SUPERSEDED fix-bh-met-elem-fp-char-zero-k2-split -> fix-bhmet-elem-fp-char-zero-k2-split
SUPERSEDED fix-bh-met-elem-fpk2-local-quillen-ideal -> fix-bhmet-elem-fpk2-local-quillen-ideal
SUPERSEDED fix-bh-met-elem-fpk2-stab-diag-endpoint -> fix-bhmet-elem-fpk2-stab-diag-endpoint
SUPERSEDED fix-bh-met-envelope-cantor-action -> fix-bhmet-envelope-cantor-action
SUPERSEDED fix-bh-met-envelope-finite-index-abel -> fix-bhmet-envelope-finite-index-abel
SUPERSEDED fix-bh-met-envelope-gen-torsion-nakayama -> fix-bhmet-envelope-gen-torsion-nakayama
SUPERSEDED fix-bh-met-envelope-higman-v-gen-family -> fix-bhmet-envelope-higman-v-gen-family
SUPERSEDED fix-bh-met-envelope-higman-v-swap-gen-all -> fix-bhmet-envelope-higman-v-swap-gen-all
SUPERSEDED fix-bh-met-pure-char-prime-e-base -> fix-bhmet-pure-char-prime-e-base
SUPERSEDED fix-bh-met-pure-char-prime-e-high-artin-hasse-alg -> fix-bhmet-pure-char-prime-e-high-artin-hasse-alg
SUPERSEDED fix-bh-met-pure-char-prime-e-high-coprimary-fp -> fix-bhmet-pure-char-prime-e-high-coprimary-fp
SUPERSEDED fix-bh-met-pure-char-prime-e-high-witt-e-base -> fix-bhmet-pure-char-prime-e-high-witt-e-base
SUPERSEDED fix-bh-met-pure-char-prime-e-high-witt-e-coeff -> fix-bhmet-pure-char-prime-e-high-witt-e-coeff
SUPERSEDED fix-bh-met-pure-char-zero-cocycle -> fix-bhmet-pure-char-zero-cocycle
SUPERSEDED fix-bh-met-pure-char-zero-matrix -> fix-bhmet-pure-char-zero-matrix
SUPERSEDED fix-bh-met-torsion-free-coprimary-block -> fix-bhmet-torsion-free-coprimary-block
SUPERSEDED fix-bh-met-torsion-free-noether-localize -> fix-bhmet-torsion-free-noether-localize

## Pending build verdict: unwired Lean landed by the 16:10 sweep (no fix node until a probe says red)
PENDING GroupApproximation/BHPalomar/GraphProducts/Twist.lean bh-pal-graphprod
PENDING GroupApproximation/BHPalomar/GraphProducts/Statement.lean bh-pal-graphprod
PENDING GroupApproximation/BHPalomar/GraphProducts/FreeProductMap.lean bh-pal-graphprod
PENDING GroupApproximation/BHPalomar/GraphProducts/Semidirect.lean bh-pal-graphprod
PENDING GroupApproximation/Kourovka1759/Statement.lean bh-pal-kourovka57
PENDING GroupApproximation/ClassTransposition/Out/Flip.lean bh-pal-kourovka57
PENDING GroupApproximation/ClassTransposition/Out/Outer.lean bh-pal-kourovka57
PENDING GroupApproximation/Kourovka1759/Chain.lean bh-pal-kourovka59
PENDING GroupApproximation/Kourovka1759/Swap.lean bh-pal-kourovka59
PENDING GroupApproximation/Kourovka1759/Graft.lean bh-pal-kourovka59
PENDING GroupApproximation/Kourovka1759/PC.lean bh-pal-kourovka59
PENDING GroupApproximation/Kourovka1759/Base.lean bh-pal-kourovka59
PENDING GroupApproximation/Kourovka1759/Statement.lean bh-pal-kourovka59
PENDING GroupApproximation/Kourovka1759/Meq.lean bh-pal-kourovka59
PENDING GroupApproximation/Kourovka1759/Tree.lean bh-pal-kourovka59
PENDING GroupApproximation/Kourovka1759/Equi.lean bh-pal-kourovka59
PENDING GroupApproximation/Kourovka1759/Box.lean bh-pal-kourovka59
PENDING GroupApproximation/Kourovka1759/Main.lean bh-pal-kourovka59
PENDING GroupApproximation/BooneHigmanLinear/CharZero/Leaves.lean bh-pal-linear-char0
PENDING GroupApproximation/BooneHigmanLinear/CharZero/SIntSuslin.lean bh-pal-linear-char0
PENDING GroupApproximation/BooneHigmanLinear/CharZero/Frontier.lean bh-pal-linear-char0
PENDING GroupApproximation/BooneHigmanLinear/CharZero/FrontierRankFour.lean bh-pal-linear-char0
PENDING GroupApproximation/BooneHigmanLinear/CharP/OneVariableHost.lean bh-pal-linear-charp
PENDING GroupApproximation/BooneHigmanLinear/CharP/LowTrdegCoords.lean bh-pal-linear-charp
PENDING GroupApproximation/BooneHigmanLinear/FrontierFour.lean bh-pal-wire
PENDING GroupApproximation/Manuscript/NonMF/Full/NMRegradeA/TransientAtomSentences.lean ms-nm-partial-a
PENDING GroupApproximation/Manuscript/NonMF/Full/NMRegradeA/InvolutionAtomBlocks.lean ms-nm-partial-a
PENDING GroupApproximation/Manuscript/SimpleKazhdanSofic/SkOpen/Arzhantseva.lean ms-sk-open
PENDING GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVPolyK2/Basic.lean ms-sk-uncond-a
PENDING GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/SKAttestB/WordProblems.lean ms-sk-uncond-b
PENDING GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/SKAttestB/LEFHosts.lean ms-sk-uncond-b
