---
rg: 2
id: weak-mf-embedding-not-reusable
kind: claim
title: A given weak-MF embedding can never be re-metrized into a hyperlinear one
distinct_from:
  corner-renormalization-cost: That claim measures compression; this one says that the two operations available on a *fixed* model --- changing the metric and amplifying --- provably cannot produce trace visibility.
  mf-implies-hyperlinear: That root is about existence of some model; this claim rules out one whole family of proof strategies for it, and is established.
artifacts:
  - GroupApproximation/Sofic/NormTraceGap.lean
  - notes/NOTEPAD.md
  - notes/NON_MF_ARCHAEOLOGY.md
---

Three established facts, each formalized or witnessed explicitly, jointly
close the "reuse the given embedding" family of strategies for
`mf-implies-hyperlinear`.

1. *Padding dilutes.*  Identity-block padding preserves units, products,
   adjoints and every operator-norm distance exactly, while dividing every
   Hilbert--Schmidt quantity by the relative dimension of the original block:
   `NormTraceGap.l2_opNorm_cornerPad`, `NormTraceGap.hsDistSq_padMatrix`,
   `NormTraceGap.norm_normTrace_padMatrix_sub_one_le` (the padded unitary is
   trace-invisible at rate exactly the relative dimension).

2. *Even exact representations do it.*  For irrational `theta`, the exact
   representations `1 |-> diag(exp(i theta),1,...,1)` of `Z` in `U(n)` give an
   operator-norm faithful embedding of `Z` in the norm quotient which
   converges to the identity in normalized Hilbert--Schmidt norm
   (`notes/NOTEPAD.md`, entry of 2026-08-12).  `Z` is of course hyperlinear;
   what the witness shows is that hyperlinearity cannot be obtained by
   changing the metric on a given weak-MF embedding.

3. *Amplification tracks distance to the scalars, not deviation rank.*  The
   unitary `i . 1` has invertible deviation `i . 1 - 1`, yet every tensor
   power has normalized character of modulus one:
   `NormTraceGap.phase_deviation_no_amplification`.  The invariant that
   amplification does drive is `1 - ||normTrace u||`
   (`NormTraceGap.norm_normTrace_tensorPow_le`).

Consequently any proof of `mf-implies-hyperlinear` must *select* models
(equivalently, control a rate or find an invariant corner), and any
refutation must rule out all of them.  This is also where the two MF
conventions part: Schafhauser's trace-controlled/reduced-norm MF implies
hyperlinearity by definition, while the Shulman/Carrion--Dadarlat--Eckhardt
weak convention used here does not (`notes/NOTEPAD.md`, same entry).
