---
id: fix-nm-uncond-b-torsion-free-waist
kind: claim
rg: 2
title: "Fix GroupApproximation.Manuscript.NonMF.Full.NMUncondB.TorsionFreeWaist: conditional on the two Osin 9.7(b) residuals (unprobed)"
---

**Module.** `GroupApproximation/Manuscript/NonMF/Full/NMUncondB/TorsionFreeWaist.lean`, a new unwired orphan from lane ms-nm-uncond-b. It is **unprobed**: Slurm submission is blocked for the group (SLURM-BLOCKED, 09-18 ~20:55 CDT), so no build has run. No error is known.

**Why it is here.** It is CONDITIONAL. Every theorem takes `h : TorsionFreeWaistResiduals`, the conjunction at universes `0, 0, 0` of

* `Full.GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement` (binder 5), and
* `Full.GL03DKept.gl03dKept_KeptSubwalkCoreStatement` (residual 10).

Both come from the induction step of Osin, arXiv:math/0411039v3, Lemma 9.7(b). Neither is proved on main. Through `Full.GL06.relativeGreendlinger_zero_of_allCells_of_core` they give the relative Greendlinger lemma (Osin Lemma 4.4). Through `Full.TorsionFreeEndpoints.torsionFreeEndpoints_closed_of_greendlinger` they give every torsion-free endpoint of `non_mf_groups_exist.tex`: `thm:torsion-free` with its Osin and limit-set variants, `thm:hull`, `lem:saturation`, the Fournier-Facio paragraph, `cor:regular-nonmf-algebra`, abstract tex 78–79, and introduction tex 292–293 and 303–305.

Every other input of the section is already closed on main. Hull Corollary 5.7 and Lemmas 3.5 and 5.8 are closed; the embedded bridge behind Hull Corollary 7.4 is closed; Kotowski–Ollivier, the Hyde–Lodha group, DGO 2.35 and Gerasimova–Osin 1.1 are applied closed. So these two residuals are the only open input. The reduction is the work of the GL lanes (GL06 through GL06h8, GL03D, GL03DKept, GL03DKeptProof, P10*). This module only names the interface.

**Inputs (nearest red imports).** `fix-ggt-van-kampen-greendlinger-leaf-p01-cell-junction-value-hol`, `fix-ggt-van-kampen-greendlinger-leaf-p05-region-pair-rotation`, `fix-nm-full-gl03-d-kept-walk`, `fix-nm-full-gl06b-outer-side-transport`, `fix-nm-full-gl06d-outer-monogon-diagram`. Fix those first: errors here may be knock-on.

**What it needs.**
1. A trusted build of this module and of `Full.TorsionFreeEndpoints.Closed` and `Full.NMWire2.Census`. That probe is queued for when Slurm is unblocked.
2. Producers for the two residuals.

Once both producers exist, the staged `NMUncondB/TorsionFreeUnconditional.lean` (lane work dir, `staged/`) closes everything. Its only producer-dependent code is one proof line, `torsionFreeWaistResiduals_holds := ⟨…, …⟩`, plus the two import lines for the producer modules. It then gives `relativeGreendlingerQuasiGeodesicLeastArea_closed` and `torsionFreeEndpoints_closed`, both with `#audit_closed_axioms`.

**Resolve when.** `TorsionFreeUnconditional` is green on main with `#audit_closed_axioms` clean. Then flip this node to RESOLVED and cite the green commit.
