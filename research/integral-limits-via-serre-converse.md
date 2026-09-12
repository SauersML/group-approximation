---
rg: 2
id: integral-limits-via-serre-converse
kind: route
title: The determinant conjecture plus the Serre converse gives integral spectral approximation
target: integral-group-ring-spectra-are-integral-limits
requires:
  - determinant-conjecture
  - serre-class-measures-are-integral-spectral-limits
---

The determinant conjecture puts every integral self-adjoint spectrum in the
Serre class (`determinant-conjecture-iff-serre-class-spectra`), and the
converse turns every Serre-class measure into an integral spectral limit.

This closes a cycle with `determinant-conjecture-via-integral-spectral-approximation`
on purpose. Together the two routes record that, modulo the converse, integral
spectral approximation is equivalent to the determinant conjecture. A least
fixpoint never fires a cycle, so neither claim establishes itself.
