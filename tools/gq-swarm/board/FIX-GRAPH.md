# FIX GRAPH index (Cairn fix nodes research/fix-*.md). Owner: fix-graph-lead. One line: <status> <node-id> <module> <owner-lane>
# Source: trusted MSI build of origin/main 3c8b417428 (error index work/bh-pal-integrate/scratch/errindex-3c8b417428.txt). Nodes 3b413a74c; dedupe 4edcbf1ee. 09-18 eve: main-only; lane Lean on main via 8d6acdcd0c + merge a2646f3723 (none of it in the root closure). Maintained by work/fix-graph-lead/loop3.sh.
# All 32 are leaves in that build (no red imports). Their importers did not build, so more reds will surface once these are fixed; they get new nodes with requires-edges.
# BH repairs: bh-pal-wire has repairs in its work dir for all 27 (FrontierFour probe queued). SK: ms-green-sk.

## Open
UNPROBED fix-bhmet-envelope-cantor-action GroupApproximation.BooneHigman.Metabelian.EnvelopeCantorAction bh-pal-wire -- repair landed d2df12ed90 (unprobed)
UNPROBED fix-bhmet-envelope-higman-v-gen-family GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVGenFamily bh-pal-wire -- repair landed d2df12ed90 (unprobed)
UNPROBED fix-bhmet-envelope-higman-v-swap-gen-all GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVSwapGenAll bh-pal-wire -- repair landed d2df12ed90 (unprobed)
UNPROBED fix-bhmet-affine-fp-identities GroupApproximation.BooneHigman.Metabelian.AffineFPIdentities bh-pal-wire -- repair landed d2df12ed90 (unprobed)
UNPROBED fix-bhmet-envelope-gen-torsion-nakayama GroupApproximation.BooneHigman.Metabelian.EnvelopeGenTorsionNakayama bh-pal-wire -- repair landed d2df12ed90 (unprobed)
UNPROBED fix-bhmet-pure-char-prime-e-high-coprimary-fp GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighCoprimaryFp bh-pal-wire -- repair landed d2df12ed90 (unprobed)
UNPROBED fix-bhmet-torsion-free-coprimary-block GroupApproximation.BooneHigman.Metabelian.TorsionFreeCoprimaryBlock bh-pal-wire -- repair landed d2df12ed90 (unprobed)
UNPROBED fix-sk-leavitt-k2-field-two-action GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwoAction ms-green-sk -- fix on main in 8d6acdcd0c/a2646f3723 (bytes = lane overlay); covers every error of errindex-3c8b417428; probe 1789778222 queued, SLURM-BLOCKED (repair landed 8d6acdcd0c)
UNPROBED fix-bhmet-coprimary-module GroupApproximation.BooneHigman.Metabelian.CoprimaryModule bh-pal-wire -- repair landed d2df12ed90 (unprobed)
UNPROBED fix-bhmet-pure-char-prime-e-high-witt-e-coeff GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittECoeff bh-pal-wire -- repair landed d2df12ed90 (unprobed) (repair landed 55aba370a4)
UNPROBED fix-sk-sk-rows-steinberg-weyl-diagonal GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.SteinbergWeyl.Diagonal ms-green-sk -- fix on main in 8d6acdcd0c/a2646f3723 (bytes = lane overlay); covers every error of errindex-3c8b417428; probe 1789778222 queued, SLURM-BLOCKED (repair landed 8d6acdcd0c)
UNPROBED fix-bhmet-char-p-host-tree-word GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeWord bh-pal-wire -- repair landed d2df12ed90 (unprobed)
UNPROBED fix-bhmet-char-zero-host-letters GroupApproximation.BooneHigman.Metabelian.CharZeroHost.Letters bh-pal-wire -- repair landed d2df12ed90 (unprobed)
UNPROBED fix-bhmet-char-p-host-carry-recursion GroupApproximation.BooneHigman.Metabelian.CharPHost.CarryRecursion bh-pal-wire -- repair landed d2df12ed90 (unprobed)
UNPROBED fix-bhmet-pure-char-prime-e-high-witt-e-base GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittEBase bh-pal-wire -- repair landed d2df12ed90 (unprobed)
UNPROBED fix-bhmet-affine-fp-model GroupApproximation.BooneHigman.Metabelian.AffineFPModel bh-pal-wire -- repair landed d2df12ed90 (unprobed) (repair landed 55aba370a4)
UNPROBED fix-bhmet-char-p-coords-free-mul GroupApproximation.BooneHigman.Metabelian.CharPCoordsFreeMul bh-pal-wire -- repair landed d2df12ed90 (unprobed)
UNPROBED fix-bhmet-pure-char-zero-matrix GroupApproximation.BooneHigman.Metabelian.PureCharZeroMatrix bh-pal-wire -- repair landed d2df12ed90 (unprobed)
UNPROBED fix-bhmet-char-p-coords-assembly GroupApproximation.BooneHigman.Metabelian.CharPCoordsAssembly bh-pal-wire -- repair landed d2df12ed90 (unprobed)
UNPROBED fix-bhmet-pure-char-prime-e-base GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEBase bh-pal-wire -- repair landed d2df12ed90 (unprobed)
UNPROBED fix-bhmet-pure-char-zero-cocycle GroupApproximation.BooneHigman.Metabelian.PureCharZeroCocycle bh-pal-wire -- repair landed d2df12ed90 (unprobed)
UNPROBED fix-sk-leavitt-k2-padded-central-matrix-id GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.MatrixId ms-green-sk -- fix on main in 8d6acdcd0c/a2646f3723 (bytes = lane overlay); covers every error of errindex-3c8b417428; probe 1789778222 queued, SLURM-BLOCKED (repair landed 8d6acdcd0c)
UNPROBED fix-sk-leavitt-k2-row-column-vec-prod GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.RowColumn.VecProd ms-green-sk -- fix on main in 8d6acdcd0c/a2646f3723 (bytes = lane overlay); covers every error of errindex-3c8b417428; probe 1789778222 queued, SLURM-BLOCKED (repair landed 8d6acdcd0c)
UNPROBED fix-bhmet-torsion-free-noether-localize GroupApproximation.BooneHigman.Metabelian.TorsionFreeNoetherLocalize bh-pal-wire -- repair landed d2df12ed90 (unprobed)
UNPROBED fix-bhmet-pure-char-prime-e-high-artin-hasse-alg GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighArtinHasseAlg bh-pal-wire -- repair landed d2df12ed90 (unprobed) (repair landed 55aba370a4)
UNPROBED fix-bhmet-envelope-finite-index-abel GroupApproximation.BooneHigman.Metabelian.EnvelopeFiniteIndexAbel bh-pal-wire -- repair landed d2df12ed90 (unprobed)
UNPROBED fix-bhmet-absorption-suslin-euclid-kill GroupApproximation.BooneHigman.Metabelian.AbsorptionSuslinEuclidKill bh-pal-wire -- repair landed d2df12ed90 (unprobed)
UNPROBED fix-sk-leavitt-k2-padded-central-vectors GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.Vectors ms-green-sk -- fix on main in 8d6acdcd0c/a2646f3723 (bytes = lane overlay); covers every error of errindex-3c8b417428; probe 1789778222 queued, SLURM-BLOCKED (repair landed 8d6acdcd0c)
UNPROBED fix-bhmet-char-zero-coords-denominators GroupApproximation.BooneHigman.Metabelian.CharZeroCoordsDenominators bh-pal-wire -- repair landed 90089df2a1 (unprobed)
UNPROBED fix-bhmet-elem-fp-char-zero-k2-split GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2Split bh-pal-wire -- repair landed d2df12ed90 (unprobed)
UNPROBED fix-bhmet-elem-fpk2-stab-diag-endpoint GroupApproximation.BooneHigman.Metabelian.ElemFPK2StabDiagEndpoint bh-pal-wire -- repair landed d2df12ed90 (unprobed)
UNPROBED fix-bhmet-elem-fpk2-local-quillen-ideal GroupApproximation.BooneHigman.Metabelian.ElemFPK2LocalQuillenIdeal bh-pal-wire -- repair landed d2df12ed90 (unprobed)

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
PENDING GroupApproximation/BHPalomar/GraphProducts/Twist.lean bh-pal-graphprod (landed ab84f925c9)
PENDING GroupApproximation/BHPalomar/GraphProducts/Statement.lean bh-pal-graphprod (landed 8d6acdcd0c)
PENDING GroupApproximation/BHPalomar/GraphProducts/FreeProductMap.lean bh-pal-graphprod (landed 70e4d3e8e4)
PENDING GroupApproximation/BHPalomar/GraphProducts/Semidirect.lean bh-pal-graphprod (landed ab84f925c9)
PENDING GroupApproximation/Kourovka1759/Statement.lean bh-pal-kourovka57 (landed 1284827709)
PENDING GroupApproximation/ClassTransposition/Out/Flip.lean bh-pal-kourovka57 (landed 8d6acdcd0c)
PENDING GroupApproximation/ClassTransposition/Out/Outer.lean bh-pal-kourovka57 (landed 1284827709)
PENDING GroupApproximation/Kourovka1759/Chain.lean bh-pal-kourovka59 (landed 73b6d29d3e)
PENDING GroupApproximation/Kourovka1759/Swap.lean bh-pal-kourovka59 (landed 73b6d29d3e)
PENDING GroupApproximation/Kourovka1759/Graft.lean bh-pal-kourovka59 (landed 73b6d29d3e)
PENDING GroupApproximation/Kourovka1759/PC.lean bh-pal-kourovka59 (landed 73b6d29d3e)
PENDING GroupApproximation/Kourovka1759/Base.lean bh-pal-kourovka59 (landed 73b6d29d3e)
PENDING GroupApproximation/Kourovka1759/Statement.lean bh-pal-kourovka59
PENDING GroupApproximation/Kourovka1759/Meq.lean bh-pal-kourovka59 (landed 73b6d29d3e)
PENDING GroupApproximation/Kourovka1759/Tree.lean bh-pal-kourovka59 (landed 73b6d29d3e)
PENDING GroupApproximation/Kourovka1759/Equi.lean bh-pal-kourovka59 (landed 73b6d29d3e)
PENDING GroupApproximation/Kourovka1759/Box.lean bh-pal-kourovka59 (landed 73b6d29d3e)
PENDING GroupApproximation/Kourovka1759/Main.lean bh-pal-kourovka59 (landed 73b6d29d3e)
PENDING GroupApproximation/BooneHigmanLinear/CharZero/Leaves.lean bh-pal-linear-char0 (landed d01c1aebff)
PENDING GroupApproximation/BooneHigmanLinear/CharZero/SIntSuslin.lean bh-pal-linear-char0 (landed d01c1aebff)
PENDING GroupApproximation/BooneHigmanLinear/CharZero/Frontier.lean bh-pal-linear-char0 (landed d01c1aebff)
PENDING GroupApproximation/BooneHigmanLinear/CharZero/FrontierRankFour.lean bh-pal-linear-char0 (landed d01c1aebff)
PENDING GroupApproximation/BooneHigmanLinear/CharP/OneVariableHost.lean bh-pal-linear-charp (landed d6f9688298)
PENDING GroupApproximation/BooneHigmanLinear/CharP/LowTrdegCoords.lean bh-pal-linear-charp (landed d6f9688298)
PENDING GroupApproximation/BooneHigmanLinear/FrontierFour.lean bh-pal-wire (landed d2df12ed90)
PENDING GroupApproximation/Manuscript/NonMF/Full/NMRegradeA/TransientAtomSentences.lean ms-nm-partial-a (landed f7e7fbf920)
PENDING GroupApproximation/Manuscript/NonMF/Full/NMRegradeA/InvolutionAtomBlocks.lean ms-nm-partial-a (landed f7e7fbf920)
PENDING GroupApproximation/Manuscript/SimpleKazhdanSofic/SkOpen/Arzhantseva.lean ms-sk-open (landed e7fff6d62e)
UNPROBED GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVPolyK2/Basic.lean ms-sk-uncond-a (on main; SLURM-BLOCKED)
UNPROBED GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/SKAttestB/WordProblems.lean ms-sk-uncond-b (on main f05181e78; Slurm blocked 09-18 19:40; probe 1789778224 DEFERRED (sbatch AssocMaxSubmitJobLimit); not root-wired)
UNPROBED GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/SKAttestB/LEFHosts.lean ms-sk-uncond-b (on main f05181e78; Slurm blocked 09-18 19:40; probe 1789778224 DEFERRED (sbatch AssocMaxSubmitJobLimit); not root-wired)
UNPROBED GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/SKAttestA/Intro.lean ms-sk-uncond-a (on main; SLURM-BLOCKED)
UNPROBED GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/SKAttestA/General.lean ms-sk-uncond-a (on main; SLURM-BLOCKED)

## Pending build verdict: Lean added by 8d6acdcd0c / merge a2646f3723 (09-18 eve)
PENDING GroupApproximation/BHPalomar/GraphProducts/Embedding.lean bh-pal-graphprod (landed ab84f925c9)
PENDING GroupApproximation/BHPalomar/GraphProducts/Insert.lean bh-pal-graphprod (landed ab84f925c9)
PENDING GroupApproximation/BHPalomar/GraphProducts/Main.lean bh-pal-graphprod (landed 8d6acdcd0c)
PENDING GroupApproximation/BHPalomar/GraphProducts/ProductClosure.lean bh-pal-graphprod (landed aaf03f7cae)
PENDING GroupApproximation/BHPalomar/GraphProducts/ProductInput.lean bh-pal-graphprod (landed ab84f925c9)
PENDING GroupApproximation/BHPalomar/GraphProducts/Reduction.lean bh-pal-graphprod (landed aaf03f7cae)
PENDING GroupApproximation/BHPalomar/GraphProducts/Restrict.lean bh-pal-graphprod (landed ab84f925c9)
PENDING GroupApproximation/BooneHigman/Join/HigmanVCalibCore.lean bh-pal-met-join (landed 8d6acdcd0c)
PENDING GroupApproximation/BooneHigman/Join/HigmanVCalibration.lean bh-pal-met-join (landed 8d6acdcd0c)
PENDING GroupApproximation/ClassTransposition/Presentation/Basic.lean bh-pal-kourovka61 (landed 8d6acdcd0c)
PENDING GroupApproximation/Manuscript/NonMF/Full/GL03C/Endpoint.lean ms-green-nm (landed 07f65e67e7)
UNPROBED GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVAssembly/Endpoint.lean ms-sk-uncond-a (repaired 8bb2199cc2, conditional; SLURM-BLOCKED)
UNPROBED GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVCohnK2/Final.lean ms-sk-uncond-a (repaired 8bb2199cc2, conditional; SLURM-BLOCKED)
PENDING GroupApproximation/Manuscript/SimpleKazhdanSofic/SkOpen/BooneHigmanThompson.lean ms-sk-open (landed 8d6acdcd0c)
OPEN fix-sk-cohn-stable-k2-degree-zero-surj (SK open row gate: skCohnLimK2_degreeZeroSurjStatement; node 89031424b5) ms-sk-uncond-a
UNPROBED (new module, no fix node) GroupApproximation.Manuscript.SimpleKazhdanSofic.SkOpen.Arzhantseva ms-sk-open -- on main e7fff6d62e (bytes = lane file); SK census aaf5fe1a98c3; NOT root-wired; probe request 1789778213.65131 queued (SLURM-BLOCKED)
UNPROBED (new module, no fix node) GroupApproximation.Manuscript.SimpleKazhdanSofic.SkOpen.BooneHigmanThompson ms-sk-open -- on main 8d6acdcd0c (bytes = lane file); SK census 9fe4e2896405; NOT root-wired; same probe request
UNPROBED GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVPolyK2/Localization.lean ms-sk-uncond-a (00afa94386; SLURM-BLOCKED)
UNPROBED GroupApproximation/BooneHigman/Metabelian/EnvelopeGenTorsion.lean bh-pal-wire (landed 90089df2a1, unprobed; not root-wired)
UNPROBED GroupApproximation/BooneHigman/Metabelian/EnvelopeWreathEmbedConeV.lean bh-pal-wire (landed 90089df2a1, unprobed; not root-wired)
UNPROBED GroupApproximation/BooneHigman/Metabelian/AbsorptionSuslinReduction.lean bh-pal-wire (landed 55aba370a4, unprobed; not root-wired)
UNPROBED GroupApproximation/BooneHigman/Metabelian/AffineFPConjugation.lean bh-pal-wire (landed 55aba370a4, unprobed; not root-wired)
UNPROBED GroupApproximation/BooneHigman/Metabelian/CharPHost/TreeFaithful.lean bh-pal-wire (landed 55aba370a4, unprobed; not root-wired)
UNPROBED GroupApproximation/BooneHigman/Metabelian/CharPHost/TreeGroup.lean bh-pal-wire (landed 55aba370a4, unprobed; not root-wired)
UNPROBED GroupApproximation/BooneHigman/Metabelian/CharZeroHost/State.lean bh-pal-wire (landed 55aba370a4, unprobed; not root-wired)
UNPROBED GroupApproximation/BooneHigman/Metabelian/CoprimarySplitting.lean bh-pal-wire (landed 55aba370a4, unprobed; not root-wired)
UNPROBED GroupApproximation/BooneHigman/Metabelian/EnvelopeSimpleFragCantor.lean bh-pal-wire (landed 55aba370a4, unprobed; not root-wired)
UNPROBED GroupApproximation/BooneHigman/Metabelian/EnvelopeWreathEmbed.lean bh-pal-wire (landed 55aba370a4, unprobed; not root-wired)
UNPROBED GroupApproximation/BooneHigman/Metabelian/PureCharPrimeSplit.lean bh-pal-wire (landed 55aba370a4, unprobed; not root-wired)
UNPROBED GroupApproximation/BooneHigman/Metabelian/SuslinZHalfEndpoint.lean bh-pal-wire (landed 55aba370a4, unprobed; not root-wired)
UNPROBED GroupApproximation/BooneHigman/Metabelian/SuslinZLocalEndpoint.lean bh-pal-wire (landed 55aba370a4, unprobed; not root-wired)
OPEN fix-bhpalomar-graphproducts-main GroupApproximation.BHPalomar.GraphProducts.Main bh-pal-graphprod -- conditional on EnvelopeInput (BFFHZ Thm C+E); chain unprobed (Slurm blocked); landed aaf03f7cae
