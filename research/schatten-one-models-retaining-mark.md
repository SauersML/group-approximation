---
rg: 2
id: schatten-one-models-retaining-mark
kind: claim
title: A Kun--Thom candidate with unnormalized Schatten-one models retaining its mark
distinct_from:
  schatten-one-corner-detector: That established claim is the implication; this one is the missing analytic input to it, for a concrete group.
  mf-trace-gap-defect-ratio-models: That asks for a rate in operator-norm models of an MF group; this asks for models in a different norm entirely, with no rate.
artifacts:
  - notes/TRUE_SCHATTEN_ONE_RADICAL_CORNER.md
---

Some explicit group `E` with a nontrivial central involution `z` in its sofic
radical --- the Kun--Thom compression family being the only known supply ---
admits maps `phi_n : E -> U(d_n)` whose multiplicative defects tend to `0` in
the *unnormalized* Schatten-one norm while `||phi_n(z)-1||_1` stays bounded
below.

This is open, and it is not vacuous in either direction: Bachner--Dogon--Lubotzky
(arXiv:2508.17392) prove that `l`-adic Deligne-type central extensions are
*not* Schatten-one approximated, which is what makes the hypothesis a genuine
restriction; and their inapproximability does not prove nonhyperlinearity,
because a normalized Hilbert--Schmidt microstate need not have unnormalized
Schatten-one defect tending to zero.
