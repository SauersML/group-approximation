# bh-pal-met-join
Direction: T2 (metabelian BH) — take unowned ChainWiredFrontierThree gaps; new modules under GroupApproximation/BooneHigman/Join/.
- 09-18 15:40 CDT start. All six open gap families are >2 h stale (latest BooneHigman commit 18:07 UTC). Route A of the chain now waits on exactly four open statements (ElemFPBhNagaoWireUncondTop): S1 Suslin bad-prime local, P1 char-p K2 gap pair, Z1 char-0 K2 split gap (needs Behr/Tate arithmetic of Z[1/m]), H1 Higman-V Step-B core (HigmanVCStepBCoreStatement).
- Picked H1 (gap 8): the only one with an elementary (non-arithmetic) proof.
- Probe (build-grade the V-side of gap 8): StepBReduce, CommonCentral, SwindleProd, SwindleIndep. Result below when it lands.
- 15:5x probe DEFERRED: the Mac had under 3 GiB free (the disk is at 98-99%). No build grade yet for the V-side modules. Coordinator: disk.
- 16:1x LANDED cbcd58208 `higman-v-step-b-core-local-conjugation-and-f-obstruction` (paper lane proof, not Lean).
  - A: C-local balanced u gives h u h^-1 = u^pi in Q.
  - B: this settles every per-cycle-symmetrizable core instance, strictly extending 93f's symmetric case.
  - C: an explicit d=2 instance (C={0,10,11}, h=l(0,10), P=split l(0,1000)) meets every core hypothesis, has no such data, and E(hP) has infinite order.
  - Verdict: H1 needs a Thompson-F normal form. The calibration identity l(0,10)l(0,1000)=l(00,10)*sigma is written out.
- S1 (suslinZLocal_BadStatement) assessed and NOT attempted. Its content is the local step of Suslin's SL_n = E_n over Z[1/m][x's] at bad primes. Nagata's trick leaves a non-unit integer leading coefficient, and the one-sided version is refuted (93p). This is research-scale commutative algebra, with no short route.
- Next for whoever takes H1:
  (1) Find the derivation of the calibration identity by a bounded Knuth-Bendix/coset search (Slurm msismall), then write it as a Lean certificate.
  (2) Build the F normal form in Q.
  (3) Read Bleak-Quick's completeness proof at source.
