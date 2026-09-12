---
rg: 2
id: stw99-lxvi-finite-nonstably-finite-car-seed
kind: claim
title: A simple finite non-stably-finite algebra contains a unital CAR algebra
distinct_from:
  stw99-lxvi-finite-car-corner-with-infinite-double: this asks only that some matrix amplification be infinite; it does not prescribe the first infinite amplification or require the double itself to be infinite.
---

There exists a simple unital C-star algebra `A` such that

1. `1_A` is finite;
2. `A` is not stably finite; and
3. the CAR algebra embeds unitally in `A`.

By `stw99-lxvi-finite-car-seed-amplification-index-is-irrelevant`, this is an
equivalent, amplification-free construction target for STW Problem LXVI.

## Attempts

Tensoring a known finite but non-stably-finite simple seed with the CAR
algebra is not viable: `stw99-lxvi-car-stabilization-destroys-finite-seed`
shows that the resulting unit is infinite.  The CAR algebra must instead be
installed internally while the original finite unit is retained.  Reduced
products can assemble all dyadic matrix stages, but
`stw99-lxvi-dyadic-stage-ultraproduct-is-not-simple` records the unresolved
simplicity defect.  The present reduction helps by allowing the first
infinite amplification to occur at any matrix size; it does not assume that
the double is already infinite.
