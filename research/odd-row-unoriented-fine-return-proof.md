---
rg: 2
id: odd-row-unoriented-fine-return-proof
kind: route
title: Decompose the Whitehead image into the two controller orientations
target: odd-row-unoriented-fine-return-has-quarter-floor
requires:
  - primitive-clifford-type-fixes-orientation-not-return
  - odd-selector-row-balances-or-kills-outer-action
---

Compress `(t-WrW^*)W e z_+` to `z_+` and `z_-`.  The relation `re=-e`
turns it into `(1+t)W e z_+`; the two compressions are respectively twice
the wrong fine-support piece in the positive orientation and twice the fine
piece in the negative orientation.  The unoriented support error contains
all remaining pieces except `fz_+`.  Since `fz_+` has only half the trace
capacity of `ez_+`, the uncovered mass is at least `tau(z_+)/4`.  Finite
packet exactification and a fixed contraction telescope give `(OUF7)`.

