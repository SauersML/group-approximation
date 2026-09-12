---
rg: 2
id: mf-convention-sofic-separation-map
kind: claim
title: Which MF conventions can separate from soficity
root: true
distinct_from:
  countable-group-mf-conventions: that orders the MF conventions among themselves; this locates each of them against soficity.
  nonsofic-mechanism-mf-classification: that classifies the lamp types of one compression mechanism by operator MF; this answers the convention-level question for all groups.
  weak-mf-does-not-imply-sofic: that is the one convention at which a separation is established; this is the whole map, including the conventions that cannot separate.
---

ESTABLISHED.  The question "is there an MF group which is not sofic?" has the
following answer, convention by convention.

| MF convention | against soficity |
| --- | --- |
| operator MF (every equivalent weak norm-corona form) | **separates**: `weak-mf-does-not-imply-sofic` |
| PMatF, trace-free PPermF, trace-PMF, PFF, PPF | **cannot separate**: each forces soficity, `pure-mf-conventions-imply-sofic` |
| MF embedding of the full group C-star algebra | **cannot separate through the known mechanism**: a strict Kazhdan compressor makes the full algebra infinite, `maximal-group-cstar-infinite-under-strict-compression` |
| MF reduced group C-star algebra | **a separation is at least a Q3.4 answer**: visibility off `R_a(G)`, hyperlinearity for finite `R_a(G)`, and the dichotomy `reduced-mf-nonsofic-group-dichotomy` |
| trace-regular MF (GKMP's MF) | **a separation is a Q3.4 answer**: trace convergence to the regular character already gives hyperlinearity |

**The compression mechanism always carries a strict compressor.**  If
`Gamma` is infranormal in `G` and every compressor normalizes `Gamma`, then the
compression semigroup lies in the normalizer and generates `G`, so `Gamma` is
normal.  In the expander-matching criterion, if `t_1 Gamma t_1^(-1) = Gamma`
then `J <= t_1^(-1) Gamma t_1 = Gamma`, so `J = Gamma cap J = 1` and the
criterion is vacuous.

**Upshot.**  The MF-versus-soficity separation is settled at operator MF.  It
is impossible for pure representation conventions, and impossible for the full
group C-star algebra of any group produced by the known nonsoficity mechanism.
At trace-regular MF, and at reduced MF with finite amenable radical, every
nonsofic example is a hyperlinear nonsofic group.  The live reduced-norm target
is `nonsofic-reduced-mf-group-finite-amenable-radical`.
