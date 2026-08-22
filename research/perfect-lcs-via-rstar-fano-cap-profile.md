---
rg: 2
id: perfect-lcs-via-rstar-fano-cap-profile
kind: route
title: Affinize a uniformly selected one-ghost Fano-cap support profile
target: perfect-completeness-constant-soundness-lcs-compiler
requires:
  - culf-mastel-oracular-2csp-perfect-gap-family
  - rstar-fano-cap-support-preserves-nonru-affine-relaxation
  - culf-mastel-rstar-uniform-fano-cap-profile
---

Use the selected cap profile to replace each `R_*` context by parity
equations cutting out its affine hull.  On halting inputs the chosen perfect
CE strategy satisfies all equations exactly.  On nonhalting inputs, every
perfect CE solution of the LCS would restrict contextwise to `R_*` and hence
contradict the Culf--Mastel constant gap.  The standard compactness step
upgrades absence of a perfect CE solution for this fixed finite LCS to the
marked approximate soundness needed by the RE-oriented Kleene route.
