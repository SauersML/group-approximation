---
rg: 2
id: universal-odometer-corners-preserve-kazhdan-hosts
kind: claim
title: Every cyclic corner of a universal-odometer subshift yields another universal Kazhdan host
distinct_from:
  simple-kazhdan-lef-hosts-all-countable-locally-finite: that constructs one fixed host; this proves that every cyclic corner of its defining ring supports the same simplicity, rigidity and universality conclusions.
artifacts:
  - research/artifacts/pestov91-universal-host-finite-centralizers-2026-09-13.md
---

Let `(X,T)` be an infinite minimal finite-alphabet subshift with compatible
onto factors `pi_n:X -> Z/nZ` for all positive `n`. Set
`R=LC(X,F_2) semidirect Z`. For each positive `m`, let
`C=pi_m^{-1}(0)`, `q=1_C` and `A=qRq`.

Then `(C,T^m)` is an infinite minimal finite-alphabet subshift with
universal odometer factor, and `A ~= LC(C,F_2) semidirect_(T^m) Z`.
Consequently `EL_3(A)` is infinite, simple, Kazhdan, LEF, and contains
every countable locally finite group.
