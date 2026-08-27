---
rg: 2
id: mf-recognition-finite-presentations-is-pi2-complete
kind: claim
title: MF and non-MF recognition are second-level complete on finite presentation codes
root: true
artifacts:
  - non_mf_groups_exist.tex
  - research/artifacts/mf-recognition-fp-pi2-completeness-2026-08-25.md
  - research/artifacts/regular-mf-tensor-sync-shulman-completion-2026-08-26.md
  - research/artifacts/mf-fp-pi2-unconditional-assembly-2026-08-26.md
distinct_from:
  mf-recognition-has-a-pi2-upper-bound: that proves the membership upper bound and properness over the first level; this asks for the missing FIN-hardness.
  mf-recognition-recursive-presentations-is-second-level-complete: that proves exact completeness before finite-presentation compilation.
---

**ESTABLISHED.**  For finite presentation codes,

```text
NONMF_fp is Sigma^0_2-complete,
MF_fp    is Pi^0_2-complete.
```

The upper bounds are established by
[[mf-recognition-has-a-pi2-upper-bound]].  The matching hardness reduction is

```text
FIN <=_m NONMF_fp.
```

It uses the exact recursive FIN/INF switch, the residually finite
three-generator bridge, a Mikhailova fiber-product benign witness whose
ambient group is a direct product of free groups, the residually finite
embedding `B3(1)<=F_2 times F_2`, and tensor synchronization of the final
asymmetric rope edge.  The output is MF on `INF` and contains the fixed non-MF
group `E` on `FIN`.

## Attempts

The finitely presented Higman host itself need not be MF.  The completed
compiler uses only its relators and marked embedding words to build a
Mikhailova subgroup in a residually finite product of free groups.  This
regular-MF witness supplies the faithful model, while the graph witness
supplies finite edge models.
Tensoring them makes the final edge compatible in operator norm.

## Independent verification and unconditional assembly (2026-08-26)

Every link of the establishing chain was re-derived in
`research/artifacts/mf-fp-pi2-unconditional-assembly-2026-08-26.md`:
switch, bridge, `N_e <= N_+`, Mikhailova cut, graph witness and finite
CEP, `(RTS1)`, the finite presentation `(T16)`, both branch verdicts, and
the completeness bookkeeping.  The analytic core was reassembled
self-containedly as [[twisted-hnn-mf-permanence-with-corona-conjugator]]
(no reduced-HNN normal form, no freeness estimate; Ueda's corner is
re-proved by a universal-property computation), with a single verified
literature input: Shulman, arXiv:2603.13564v2, **Theorem 16 in the v2
body numbering** — the v2 introduction still calls it "Th. 20" (stale v1
labels), a citation trap for the manuscript.  Two cautions recorded there:
the concrete tensor-model representation of the rope is provably NOT
faithful (the conjugator commutes with the killed Mikhailova factor), so
group injectivity must run at the universal HNN algebra; and the statement
proved is the operator-norm matricial predicate (`IsOperatorMF`, CDE) —
the trace-regular/reduced-norm strengthening remains open and lacks even a
known second-level upper bound.
