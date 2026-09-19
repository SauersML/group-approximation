# bh-pal-linear-char0
Direction: T3, the characteristic-0 half (Palomar BH megasubmission). The prefix GroupApproximation/BooneHigmanLinear/CharZero/ is mine.
- 09-18 ~15:00 finding: the char-0 coordinates (`CharZeroHost.charZeroPolynomialCoordinates`) and the affine self-similar host (`CharZeroHost.charZeroAffineSelfSimilarStatement`, `Chain.affineExtensionFPStatement_holds`) are already hypothesis-free theorems on main, by the bh-met lanes. This lane does not rebuild them. It certifies them by a trusted MSI build and wires them.
- Plan:
  (1) CharZero/Leaves.lean: bundles the three proved leaves, and reduces the char-0 linear host to the two K-theory Statements over ℤ[1/m][t̄] (absorption, E_N f.p.).
  (2) CharZero/Frontier.lean: char-0 T3 into f.p. simple groups from four gaps (hH, hgen, hcube, hswap). No char-p gap (hvdk, hloc) is needed.
  (3) CharZero/FrontierRankFour.lean: the same with hgen replaced by CZK2FngRankFourStatement (via czTriOff_posStabGen_of_rankFour).
- I do not touch the gap files. They are under active bh-met work in the other session.
- 15:40: four modules authored under work/: CharZero/{Leaves,Frontier,FrontierRankFour,SIntSuslin}.lean, namespace BooneHigmanLinear.CharZeroHalf.
  - NEW (small but real): the char-0 half of T3 needs NO char-p input. `SIntLocalHorrocksStatement` is the ℤ[1/m][t] half of the chain's two-family local Horrocks, and it alone gives Suslin SL_N = E_N over ℤ[1/m][t] (induction on k from the Euclidean base case).
  - Endpoint `charZeroLinearStatement_of_sIntFrontier (hH₀ hgen hcube hswap)`.
  - Probe queued (restart after the outage; the MSI VPN was flapping).
- For bh-pal-surface: the char-0 T3 statement is `CharZeroHalf.CharZeroLinearStatement` (∀ K [Field K] [CharZero K] n H, H.FG → EmbedsInFinitelyPresentedSimpleGroup H). It is still conditional on 4 named gaps and must not go in the megachallenge as unconditional.
