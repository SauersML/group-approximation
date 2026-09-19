# ms-sk-uncond-b
Direction: SK is UNCONDITIONAL on the non-K-theory side. Worklist item 3 is the SK attestation of the census rows at tex l.>480
(lem:nn, lem:host, lem:halfline, cor:host, cor:wp, sec:questions). ms-sk-uncond-a owns LVFreeAlg/K2/NK2 and rows l.≤480.

## Audit A: root endpoint (09-18 ~15:00)
- `Full.SKRoot.manuscript` = 27 root theorems (Full/Root/{Main,Proof,Corollaries,Intro}), all root-imported.
  Its 129 conjunct decls carry only printed hypotheses (X infinite minimal subshift; action minimal and top. free; 1 ∈ S,
  S generates; n ≥ 3; Kazhdan + not RF; simple + infinite + Kazhdan + hyperlinear). No `…Statement` appears as a binder.
- The root closure (1419 modules) has no LeavittK2/LeavittFP/Full.LV* and none of the 10:40 red modules.
- So on the non-K-theory side nothing is owed. The one `open` row (768ac9454e9b) is the K-theory side.

## Audit B: census rows l.>480 (09-18 ~15:45; files in work/ms-sk-uncond-b/)
- 81 rows: 66 formalized, 4 definition, 5 structural, 4 attribution, 1 open. The 66 formalized rows list 203 distinct decls.
- (a) EXISTS + IN ROOT CLOSURE: all 203 resolve on origin/main (res-all.tsv), in 66 modules, all inside the root import
  closure (8048 modules, rootclosure.txt). Census names are current; there are no stale renames.
- (b) NO OWED BINDER: the signatures (sigs-b.txt) were read by hand. `…Statement` appears only as a conclusion
  (lemmaNN, restrictedSumLEFStatement), and the Statement defs are plain printed claims. Every binder is a printed
  hypothesis, e.g. (hLEF : IsLEF Δ), (hfg : Group.FG Δ), (h0 : 0 < α)/(h1 : α < 1), (hWP : HasSolvableWordProblem Γ), and for
  sec:questions l.735 "a sofic example": [IsSimpleGroup Γ] [Infinite Γ] (hfp) (hT) (hsof).
- (c) AUDIT COVERAGE: 98 decls had a direct #audit line, and 105 had none (66 theorems, 32 defs, 4 structures, 2 abbrevs, 1 instance).
- FIX: new modules Full/SKAttestB/{LEFHosts,WordProblems}.lean. Each audits every decl of every row under its row:
  #audit_closed_axioms for the 23 input-free theorems, #audit_axioms otherwise. One build attests the whole range.
- Probe of both modules queued ~15:50 (Slurm).

## After the restart (09-18 19:37)
- The coordinator sweep put Full/SKAttestB/{LEFHosts,WordProblems} on main as f05181e78 (red allowed), byte-identical to my
  drafts (md5 053726bd / 9f6dfd20). FIX-GRAPH has them PENDING. They are NOT root-wired.
- No row split with ms-sk-uncond-a: SKAttestA/{Intro,General} cover tex l.33–466; SKAttestB covers l.481–738.
- Re-probe against current main (empty overlay, v4) queued 19:37: probe 1789778224.66466.
- 19:45 Slurm is blocked group-wide ($GQ/state/SLURM-BLOCKED). My one probe (queued 19:37) is still waiting and was not re-queued.
  FIX-GRAPH lines are now UNPROBED. No static fix is pending: both modules are imports plus #audit lines over resolved names.
  NEXT (once the flag is gone): read the verdict. If green, ask ms-map (item 10) to root-wire SKAttestB. If red, the likely
  cause is a closed/open misclassification: switch that line to #audit_axioms and land via gqland-lean.sh.
- 19:5x probe 1789778224 came back DEFERRED: sbatch AssocMaxSubmitJobLimit. No re-probe until SLURM-BLOCKED is gone.
