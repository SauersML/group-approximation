---
rg: 2
id: residually-p-kernels-preserve-modular-stable-finiteness
kind: claim
title: A residually finite p-group kernel preserves stable finiteness in characteristic p
distinct_from:
  modular-radical-does-not-lift-direct-finiteness: that excludes containment of the lamp augmentation ideal in the Jacobson radical; this uses separated powers of that ideal, which do not require radical containment.
  direct-finiteness-not-inherited-by-quotients: that forbids unrestricted quotient transfer; this supplies an explicit sufficient condition for lifting finiteness from a quotient.
  kun-thom-wreath-stably-finite: that now establishes all coefficient characteristics for one permutation-wreath family; this proves a general extension theorem, including nonsplit extensions, in the kernel's residual prime characteristic.
---

Let 1->N->W->G->1 be a group extension, let k have characteristic p>0,
and suppose N is residually a finite p-group: every nonidentity element
survives in some finite p-group quotient. If k[G] is stably finite, then
k[W] is stably finite. The same implication holds for direct finiteness.
No finite-generation assumption on N, splitting of the extension, or
equivariance of its finite p-group quotients is required.

In particular, for a finite p-group P and an arbitrary action G on a set X,

    k[(direct_sum_X P) semidirect G] is stably finite
       <=> k[G] is stably finite.

The reverse implication in this displayed equivalence is the extension
theorem; the forward implication uses the embedded copy of G. The action
here permutes the lamp factors. More general actions are also covered
whenever the normal kernel is residually a finite p-group.

The ring-theoretic mechanism is elementary: if J is a two-sided ideal,
intersection_(m>=1) J^m=0, and R/J is stably finite, then R is stably finite.
A reverse-inverse defect is an idempotent in J and hence belongs to every
power J^m. This does not assert J lies in the Jacobson radical or that
every 1+J element is invertible.
