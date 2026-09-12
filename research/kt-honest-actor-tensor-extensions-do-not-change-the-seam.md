---
rg: 2
id: kt-honest-actor-tensor-extensions-do-not-change-the-seam
kind: claim
title: Bernoulli and coinduced tensor extensions do not change the Kun--Thom seam class
distinct_from:
  kt-passive-mcduff-amplification-does-not-close-the-seam: that tensors by a dynamically trivial spectator; this permits an arbitrary honest action or representation of the full quotient actor on the new factor and proves that its dynamics cancels from the seam.
  kt-extrinsic-corrector-is-an-orthogonal-index-one-correspondence: that identifies the nontrivial correspondence needed; this rules out the standard Bernoulli/coinduced tensor method for producing it.
  hyperlinear-wreath-model: that asks for a genuinely coupled microstate model of the nonsofic generalized wreath; this proves why tensoring the existing AFP model with an independently constructed sofic or Bernoulli actor model cannot supply such a coupling.
---

**ESTABLISHED TENSOR-EXTENSION NO-GO.**  Let `q:P_A->G` be the quotient and
let

```text
sigma:G->U(Q)
```

be any honest unitary representation in a finite tracial algebra, or the
canonical implementing representation of any p.m.p., Bernoulli, coinduced,
or McDuff action of `G`.  Tensor the AFP lift by

```text
u'_p=u_p tensor sigma_(q(p)).                            (KAT1)
```

Then its mixed seam cocycle is exactly

```text
k'_gamma=k_gamma tensor 1.                              (KAT2)
```

Indeed the quotient representation already satisfies

```text
sigma_C sigma_gamma sigma_C^*=sigma_(alpha_C(gamma)),
```

so its contribution cancels when the two Gamma implementations are divided.
Consequently no independent honest actor tensor factor changes the
coboundary problem.  If the new factor is used only through its relative
commutant, `kt-passive-mcduff-amplification-does-not-close-the-seam` retains
the same Kazhdan gap.

The standard three-block idea is a special case of the same firewall when
it genuinely respects all actor relators: once the block permutation is an
honest representation of `G`, it cancels from `(KAT2)`.  If it is arranged
only to satisfy `C^3` and swap the two Gamma copies, it is not an honest
representation of `S=<A,C>` and fails the finite relator part of `(KES2)`.
Thus a successful coinduced construction must couple the old and new factors
non-tensorially so as to create the orthogonal correspondence `(KBC2)`;
constructing that coupling is precisely the mixed-kernel problem, not a
Bernoulli permanence shortcut.

DERIVATION
kt-honest-actor-tensor-seam-cancellation-proof
