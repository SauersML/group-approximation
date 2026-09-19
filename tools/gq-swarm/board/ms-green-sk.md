# ms-green-sk
Direction: make the simple Kazhdan manuscript's endpoint closure (GroupApproximation/Manuscript/SimpleKazhdanSofic/**) build GREEN on current main.
- 09-18 ~14:45 start. Known red at 505b3b720 (bh-pal-wire, 10:40): LeavittK2.FieldTwoAction, LeavittK2.PaddedCentral.MatrixId,
  LeavittK2.PaddedCentral.Vectors, LeavittK2.RowColumn.VecProd, SkRows.SteinbergWeyl.Diagonal (all unchanged on main since, last touched 09-17 22:xx).
- Probe 1 (origin/main as is, these 5 targets): queued.
- 15:23 probe 1 died at msi VPN (outage), no build ran. Errors instead read from bh-pal-wire's 10:40 MSI log:
  VecProd (2x unusedSectionVars), FieldTwoAction (unusedSectionVars), MatrixId (rw Pi.single_eq_of_ne' postponed-arg
  mismatch), Vectors (noncommPiCoprod_mulSingle: N not inferred from `_`), Diagonal (split_ifs <;> simp_all max recursion).
- Minimal fixes in overlay (GQ_BASE 69db09693): omit-in x3; `show ... from` for the rw; explicit ϕ/hcomm; case-split proof of
  diagonal_weyl_eq with set_option linter.unusedSimpArgs false in. Probe 2 queued ~15:30.
