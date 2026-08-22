---
rg: 2
id: standard-reflection-sector-bcs-groupifier
kind: claim
title: Put one gapped BCS on the common high-rank side of a standard reflection type
distinct_from:
  signed-hecke-compatible-projection-atlas-for-nonce-bcs: that asks for a unital model on an entire primitive signed corner; this permits a harmless one-dimensional defect and asks for the BCS only on its common complement.
  canonical-high-density-local-sector-groupifier: that allows arbitrary local sectors and must also solve their density/meet bookkeeping; this fixes one explicit common sector whose deficit is already below the analytic threshold.
---

OPEN.  Fix a finite BCS with finite-dimensional gap `Delta>0` and a perfect
commuting model.  Choose `n` so large that

```text
1/(n-1)<Delta/(1+Delta).                                  (SRG1)
```

For the standard `S_n` type and the projections `e,q<=p` of
`standard-type-thin-common-reflection-sector`, construct a finitely presented
group containing `S_n` and finite-support group-corner packets which:

1. decode every BCS context, predicate row, and shared-variable consistency
   row on the **same** carrier `q`;
2. have normalized-HS row error `o(1)` on `q` whenever the ambient group
   relator defect is `o(1)` after exactifying the finite `S_n` packet;
3. admit one exact representation in which `p` and the required marked BCS
   carrier are nonzero.

The common-meet deficit is then exactly `tau_p(e)=1/(n-1)`, so `(SRG1)` and
`common-meet-local-sectors-pay-one-deficit` close the analytic BCS gap.  No
sum over contexts remains.

The unresolved operation is algebraic block escape: the private context
algebras must act noncommutatively beyond the finite root block while their
predicate and overlap identities hold on `q`.  Keeping every packet inside
`pC[S_n]p` gives a forbidden finite-dimensional perfect BCS model.  Ordinary
global group relators cannot simply be declared conditional on the
noncentral projection `q`; a Hecke/Morita or multi-piece corner construction
is still required.

## Attempts

- Put every context in the finite root block `pC[S_n]p`: this gives an exact
  finite-dimensional BCS representation after compression to `q`, contrary
  to the chosen gap instance.  The payload must leave that block.
- Add ordinary relators only on the desired `q` block: a group relator is a
  global unitary identity and cannot be conditioned on the noncentral
  polynomial projection `q`.  Replacing `q` by a central sign restores only
  half-density branching, not `(SRG1)`.
- Tensor an existing signed-Hecke context atlas with the standard packet:
  this preserves the rank-one defect but leaves the original cross-context
  marginal holonomy unchanged.  A positive construction must use the common
  reflection sector inside the overlap/return cell, rather than as a spectator
  amplification.
- In fact `common-reflection-defect-is-holonomy-spectator` proves that every
  unitary transporting a complete `q`-partition to another complete
  `q`-partition must preserve `q` and split block-diagonally across `e+q`.
  Hence the defect block cannot enter the accepting-corner return word at
  all.  The alternative hyperoctahedral realization
  `hyperoctahedral-reflection-common-q-context-atlas` solves every nonlinear
  local predicate and every edgewise rank match at arbitrarily high density,
  but its first cycle is still exactly the signed-Hecke block-escaping
  holonomy gate.
